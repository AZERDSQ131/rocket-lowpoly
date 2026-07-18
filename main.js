import * as THREE from "three";

/* ------------------------------------------------------------------ */
/*  Bruit de valeur 2D (déterministe par seed) — pour le terrain      */
/* ------------------------------------------------------------------ */

function makeNoise2D(seed) {
  let s = seed >>> 0;
  const rand = () => {
    s ^= s << 13; s >>>= 0;
    s ^= s >> 17;
    s ^= s << 5; s >>>= 0;
    return (s >>> 0) / 4294967296;
  };

  const gridSize = 256;
  const grid = new Float32Array(gridSize * gridSize);
  for (let i = 0; i < grid.length; i++) grid[i] = rand();

  const at = (x, y) => {
    const xi = ((x % gridSize) + gridSize) % gridSize;
    const yi = ((y % gridSize) + gridSize) % gridSize;
    return grid[yi * gridSize + xi];
  };

  const smooth = (t) => t * t * (3 - 2 * t);

  return function noise2D(x, y) {
    const x0 = Math.floor(x), y0 = Math.floor(y);
    const tx = smooth(x - x0), ty = smooth(y - y0);
    const a = at(x0, y0), b = at(x0 + 1, y0);
    const c = at(x0, y0 + 1), d = at(x0 + 1, y0 + 1);
    const top = a + (b - a) * tx;
    const bottom = c + (d - c) * tx;
    return top + (bottom - top) * ty;
  };
}

function fbm(noise2D, x, y, octaves = 4) {
  let amp = 1, freq = 1, sum = 0, norm = 0;
  for (let i = 0; i < octaves; i++) {
    sum += noise2D(x * freq, y * freq) * amp;
    norm += amp;
    amp *= 0.5;
    freq *= 2.1;
  }
  return sum / norm;
}

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function hashCell(seed, cx, cz, salt = 0) {
  let h = seed ^ 0x9e3779b9 ^ salt;
  h = Math.imul(h ^ cx, 0x85ebca6b);
  h = Math.imul(h ^ cz, 0xc2b2ae35);
  h ^= h >>> 16;
  return h >>> 0;
}

/* ------------------------------------------------------------------ */
/*  Etat global                                                        */
/* ------------------------------------------------------------------ */

const CHUNK_SIZE = 120;
const CHUNK_RES = 12;
const VIEW_RADIUS = 4; // en nombre de chunks autour du missile

const SKY_CELL_SIZE = 360;
const SKY_RADIUS = 2;

let scene, camera, renderer;
let noise2D, worldSeed;
let terrainMaterial, water;
const chunks = new Map();
const skyCells = new Map();

let rocket, flameParts, flameLight;
const smokePool = [];
const SMOKE_COUNT = 140;
let smokeTexture;

const rocketState = {
  position: new THREE.Vector3(0, 60, 0),
  velocity: new THREE.Vector3(0, 0, 0),
  // Orientation dérivée d'un cap + tangage façon avion (au lieu d'axes locaux
  // purs) : le cap tourne toujours autour de l'axe vertical du MONDE, jamais
  // brouillé par le tangage. Le tangage n'est pas borné (loopings complets)
  // et tourne autour de l'axe "droite" dérivé uniquement du cap courant.
  // Ainsi haut/bas et gauche/droite restent cohérents à toute inclinaison,
  // y compris juste après un décollage à la verticale.
  orientation: new THREE.Quaternion(),
  heading: 0, // cap (lacet), autour de l'axe monde Y
  pitchAngle: 0, // tangage libre, autour de l'axe "droite" dérivé du cap
  roll: 0,
  yawRate: 0,
  pitchRate: 0,
  thrustOn: false,
  flameIntensity: 0,
  grounded: false,
  launched: false,
};

let launcher;

let gameMode = "free"; // "free" | "target"
let targetConfig = "boatToPlane"; // "boatToPlane" | "planeToBoat" (pertinent seulement si gameMode === "target")
let menuOpen = true;
let plane, planeState;
let attachedToPlane = false; // en "planeToBoat" : le missile suit l'avion tant qu'il n'est pas lancé
let boatAlive = true; // le bateau sert de cible en "planeToBoat"

const cameraShake = { intensity: 0 };

const keys = {};

// Décalage de regard en [-1, 1], contrôlé uniquement au clic-glissé, pour
// balayer l'environnement sans jamais changer la trajectoire du missile.
const mouseLook = { x: 0, y: 0 };
let dragLooking = false;
let lastDragX = 0, lastDragY = 0;
const DRAG_LOOK_SENSITIVITY = 0.0035;
const clock = new THREE.Clock();
let sinceChunkUpdate = 999;

const cameraRig = {
  position: new THREE.Vector3(),
  lookTarget: new THREE.Vector3(),
  yaw: 0,
};

/* ------------------------------------------------------------------ */
/*  Terrain — hauteur globale                                          */
/* ------------------------------------------------------------------ */

// En mode Cible, force une zone d'océan bien dégagée autour du bateau (pas
// juste "probablement dégagée" via échantillonnage) : le terrain y est
// aplati vers un fond marin profond, avec un rayon qui dépasse la distance
// du brouillard, donc aucune terre ne peut jamais apparaître à l'horizon.
let oceanSafeZone = null; // { x, z, radius } uniquement en mode Cible

function heightAt(x, z) {
  const h = fbm(noise2D, x * 0.006 + 100, z * 0.006 + 100, 5);
  const ridge = fbm(noise2D, x * 0.015 - 50, z * 0.015 - 50, 3);
  const y = Math.pow(h, 1.4) * 70 + ridge * 12 - 20;

  if (oceanSafeZone) {
    const dx = x - oceanSafeZone.x, dz = z - oceanSafeZone.z;
    const dist = Math.sqrt(dx * dx + dz * dz);
    if (dist < oceanSafeZone.radius) {
      const t = dist / oceanSafeZone.radius;
      const blend = t * t * (3 - 2 * t); // smoothstep : 0 au centre, 1 au bord
      const deepY = WATER_LEVEL - 12;
      return deepY + (y - deepY) * blend;
    }
  }
  return y;
}

function terrainNormalAt(x, z) {
  const e = 0.75;
  const hL = heightAt(x - e, z), hR = heightAt(x + e, z);
  const hD = heightAt(x, z - e), hU = heightAt(x, z + e);
  return new THREE.Vector3(hL - hR, 2 * e, hD - hU).normalize();
}

// Cherche un point clairement immergé (mode Cible) en explorant une spirale
// autour de l'origine — garantit un bateau posé en pleine mer.
function colorForHeight(y) {
  const low = new THREE.Color(0x2e6b3e);
  const mid = new THREE.Color(0x6a8f4a);
  const high = new THREE.Color(0xcfd6d8);
  const sand = new THREE.Color(0xd8c98a);
  let c = new THREE.Color();
  if (y < -12) c.copy(sand);
  else if (y < 15) c.copy(low).lerp(mid, THREE.MathUtils.clamp((y + 12) / 27, 0, 1));
  else if (y < 45) c.copy(mid).lerp(high, THREE.MathUtils.clamp((y - 15) / 30, 0, 1));
  else c.copy(high);
  c.offsetHSL(0, 0, (Math.random() - 0.5) * 0.04);
  return c;
}

/* ------------------------------------------------------------------ */
/*  Génération de chunks (monde infini)                                */
/* ------------------------------------------------------------------ */

function createChunk(cx, cz) {
  const key = cx + "_" + cz;
  if (chunks.has(key)) return;

  const group = new THREE.Group();
  const originX = cx * CHUNK_SIZE;
  const originZ = cz * CHUNK_SIZE;

  const geometry = new THREE.PlaneGeometry(CHUNK_SIZE, CHUNK_SIZE, CHUNK_RES, CHUNK_RES);
  geometry.rotateX(-Math.PI / 2);

  const pos = geometry.attributes.position;
  const colors = new Float32Array(pos.count * 3);
  for (let i = 0; i < pos.count; i++) {
    const lx = pos.getX(i);
    const lz = pos.getZ(i);
    const y = heightAt(originX + lx, originZ + lz);
    pos.setY(i, y);
    const c = colorForHeight(y);
    colors[i * 3] = c.r;
    colors[i * 3 + 1] = c.g;
    colors[i * 3 + 2] = c.b;
  }
  geometry.computeVertexNormals();
  geometry.setAttribute("color", new THREE.BufferAttribute(colors, 3));

  const mesh = new THREE.Mesh(geometry, terrainMaterial);
  group.add(mesh);

  const rng = mulberry32(hashCell(worldSeed, cx, cz, 1));
  const decoCount = 14 + Math.floor(rng() * 16);
  for (let i = 0; i < decoCount; i++) {
    const lx = (rng() - 0.5) * CHUNK_SIZE;
    const lz = (rng() - 0.5) * CHUNK_SIZE;
    const y = heightAt(originX + lx, originZ + lz);
    const deco = makeBiomeDecoration(y, rng);
    if (!deco) continue;
    deco.position.set(lx, y, lz);
    group.add(deco);
  }

  group.position.set(originX, 0, originZ);
  scene.add(group);
  chunks.set(key, group);
}

function disposeChunk(group) {
  group.traverse((obj) => {
    if (obj.geometry) obj.geometry.dispose();
    if (obj.material && obj.material !== terrainMaterial) obj.material.dispose();
  });
}

function updateChunks(px, pz) {
  const ccx = Math.floor(px / CHUNK_SIZE);
  const ccz = Math.floor(pz / CHUNK_SIZE);
  const needed = new Set();

  for (let dx = -VIEW_RADIUS; dx <= VIEW_RADIUS; dx++) {
    for (let dz = -VIEW_RADIUS; dz <= VIEW_RADIUS; dz++) {
      const kx = ccx + dx, kz = ccz + dz;
      const key = kx + "_" + kz;
      needed.add(key);
      if (!chunks.has(key)) createChunk(kx, kz);
    }
  }

  for (const [key, group] of chunks) {
    if (!needed.has(key)) {
      scene.remove(group);
      disposeChunk(group);
      chunks.delete(key);
    }
  }
}

function clearAllChunks() {
  for (const [, group] of chunks) {
    scene.remove(group);
    disposeChunk(group);
  }
  chunks.clear();
}

/* ------------------------------------------------------------------ */
/*  Décors par biome (altitude)                                        */
/* ------------------------------------------------------------------ */

function makeBiomeDecoration(y, rng) {
  if (y < -13 || y > 68) return null;

  if (y < -2) {
    // Désert / plage
    return rng() > 0.45 ? makeCactus(rng) : makeDryBush(rng);
  }
  if (y < 24) {
    // Prairie
    const r = rng();
    if (r > 0.62) return makeTree(rng);
    if (r > 0.32) return makeBush(rng);
    return makeRock(rng);
  }
  if (y < 50) {
    // Zone rocheuse
    const r = rng();
    if (r > 0.7) return makePineTree(rng);
    return makeRock(rng);
  }
  // Sommets enneigés
  return rng() > 0.4 ? makeSnowRock(rng) : makeSpire(rng);
}

function makeTree(rng) {
  const group = new THREE.Group();
  const scale = 0.6 + rng() * 1.1;

  const trunkMat = new THREE.MeshStandardMaterial({ color: 0x5b3a24, flatShading: true });
  const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.25, 0.35, 2.2, 5), trunkMat);
  trunk.position.y = 1.1;
  group.add(trunk);

  const leafColors = [0x2f7a3f, 0x3f8f4a, 0x2a6a38];
  const leafMat = new THREE.MeshStandardMaterial({
    color: leafColors[Math.floor(rng() * leafColors.length)],
    flatShading: true,
  });
  const tiers = 2 + Math.floor(rng() * 2);
  for (let i = 0; i < tiers; i++) {
    const cone = new THREE.Mesh(new THREE.ConeGeometry(1.4 - i * 0.3, 1.8, 6), leafMat);
    cone.position.y = 2.2 + i * 1.1;
    cone.rotation.y = rng() * Math.PI;
    group.add(cone);
  }

  group.scale.setScalar(scale);
  group.rotation.y = rng() * Math.PI * 2;
  return group;
}

function makePineTree(rng) {
  const group = new THREE.Group();
  const scale = 0.7 + rng() * 1.3;
  const trunkMat = new THREE.MeshStandardMaterial({ color: 0x4a3220, flatShading: true });
  const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.18, 0.28, 3.2, 5), trunkMat);
  trunk.position.y = 1.6;
  group.add(trunk);

  const leafMat = new THREE.MeshStandardMaterial({ color: 0x27503a, flatShading: true });
  const tiers = 4;
  for (let i = 0; i < tiers; i++) {
    const cone = new THREE.Mesh(new THREE.ConeGeometry(1.1 - i * 0.2, 1.5, 6), leafMat);
    cone.position.y = 2.4 + i * 0.9;
    group.add(cone);
  }
  group.scale.setScalar(scale);
  group.rotation.y = rng() * Math.PI * 2;
  return group;
}

function makeBush(rng) {
  const group = new THREE.Group();
  const mat = new THREE.MeshStandardMaterial({ color: 0x3f7a3a, flatShading: true });
  const blobs = 2 + Math.floor(rng() * 2);
  for (let i = 0; i < blobs; i++) {
    const blob = new THREE.Mesh(new THREE.DodecahedronGeometry(0.45 + rng() * 0.35, 0), mat);
    blob.position.set((rng() - 0.5) * 0.6, 0.3 + rng() * 0.2, (rng() - 0.5) * 0.6);
    group.add(blob);
  }
  group.scale.setScalar(0.7 + rng() * 0.6);
  return group;
}

function makeDryBush(rng) {
  const group = new THREE.Group();
  const mat = new THREE.MeshStandardMaterial({ color: 0x9c8a4e, flatShading: true });
  const blobs = 2 + Math.floor(rng() * 2);
  for (let i = 0; i < blobs; i++) {
    const blob = new THREE.Mesh(new THREE.DodecahedronGeometry(0.3 + rng() * 0.3, 0), mat);
    blob.position.set((rng() - 0.5) * 0.5, 0.25 + rng() * 0.15, (rng() - 0.5) * 0.5);
    group.add(blob);
  }
  group.scale.setScalar(0.6 + rng() * 0.5);
  return group;
}

function makeCactus(rng) {
  const group = new THREE.Group();
  const mat = new THREE.MeshStandardMaterial({ color: 0x3f8f5c, flatShading: true });
  const height = 1.4 + rng() * 1.6;
  const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.28, 0.32, height, 7), mat);
  trunk.position.y = height / 2;
  group.add(trunk);

  const armCount = Math.floor(rng() * 3);
  for (let i = 0; i < armCount; i++) {
    const arm = new THREE.Mesh(new THREE.CylinderGeometry(0.16, 0.18, 0.8 + rng() * 0.5, 6), mat);
    const angle = rng() * Math.PI * 2;
    arm.position.set(Math.cos(angle) * 0.35, height * (0.4 + rng() * 0.4), Math.sin(angle) * 0.35);
    arm.rotation.z = Math.PI / 2 - 0.3;
    arm.rotation.y = angle;
    group.add(arm);
  }
  group.scale.setScalar(0.8 + rng() * 0.5);
  group.rotation.y = rng() * Math.PI * 2;
  return group;
}

function makeRock(rng) {
  const geo = new THREE.DodecahedronGeometry(0.6 + rng() * 1.2, 0);
  const mat = new THREE.MeshStandardMaterial({ color: 0x8a8a86, flatShading: true });
  const rock = new THREE.Mesh(geo, mat);
  rock.position.y = 0.3;
  rock.rotation.set(rng() * Math.PI, rng() * Math.PI, rng() * Math.PI);
  return rock;
}

function makeSnowRock(rng) {
  const group = new THREE.Group();
  const baseMat = new THREE.MeshStandardMaterial({ color: 0x8d8d8a, flatShading: true });
  const snowMat = new THREE.MeshStandardMaterial({ color: 0xf4f8fb, flatShading: true });
  const size = 0.7 + rng() * 1.3;
  const base = new THREE.Mesh(new THREE.DodecahedronGeometry(size, 0), baseMat);
  base.position.y = size * 0.4;
  base.rotation.set(rng() * Math.PI, rng() * Math.PI, rng() * Math.PI);
  group.add(base);
  const cap = new THREE.Mesh(new THREE.ConeGeometry(size * 0.7, size * 0.6, 5), snowMat);
  cap.position.y = size * 0.4 + size * 0.55;
  group.add(cap);
  return group;
}

function makeSpire(rng) {
  const mat = new THREE.MeshStandardMaterial({ color: 0xb9bcc0, flatShading: true });
  const height = 3 + rng() * 4;
  const spire = new THREE.Mesh(new THREE.ConeGeometry(0.7 + rng() * 0.5, height, 5), mat);
  spire.position.y = height / 2;
  spire.rotation.y = rng() * Math.PI;
  return spire;
}

/* ------------------------------------------------------------------ */
/*  Nuages procéduraux (infinis)                                       */
/* ------------------------------------------------------------------ */

function createSkyCell(cx, cz) {
  const key = cx + "_" + cz;
  if (skyCells.has(key)) return;

  const group = new THREE.Group();
  const rng = mulberry32(hashCell(worldSeed, cx, cz, 77));
  const originX = cx * SKY_CELL_SIZE;
  const originZ = cz * SKY_CELL_SIZE;

  const cloudCount = rng() > 0.35 ? 1 + Math.floor(rng() * 2) : 0;
  for (let i = 0; i < cloudCount; i++) {
    const cloud = makeCloud(rng);
    cloud.position.set(
      originX + (rng() - 0.5) * SKY_CELL_SIZE,
      130 + rng() * 140,
      originZ + (rng() - 0.5) * SKY_CELL_SIZE
    );
    group.add(cloud);
  }

  scene.add(group);
  skyCells.set(key, group);
}

function makeCloud(rng) {
  const group = new THREE.Group();
  const mat = new THREE.MeshStandardMaterial({ color: 0xfbfdff, flatShading: true, roughness: 1 });
  const puffs = 4 + Math.floor(rng() * 4);
  for (let i = 0; i < puffs; i++) {
    const puff = new THREE.Mesh(new THREE.IcosahedronGeometry(3 + rng() * 2.5, 0), mat);
    puff.position.set((rng() - 0.5) * 9, (rng() - 0.5) * 2, (rng() - 0.5) * 6);
    puff.scale.y = 0.6 + rng() * 0.3;
    group.add(puff);
  }
  return group;
}

function updateSkyCells(px, pz) {
  const ccx = Math.floor(px / SKY_CELL_SIZE);
  const ccz = Math.floor(pz / SKY_CELL_SIZE);
  const needed = new Set();

  for (let dx = -SKY_RADIUS; dx <= SKY_RADIUS; dx++) {
    for (let dz = -SKY_RADIUS; dz <= SKY_RADIUS; dz++) {
      const kx = ccx + dx, kz = ccz + dz;
      const key = kx + "_" + kz;
      needed.add(key);
      if (!skyCells.has(key)) createSkyCell(kx, kz);
    }
  }

  for (const [key, group] of skyCells) {
    if (!needed.has(key)) {
      scene.remove(group);
      group.traverse((o) => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
      skyCells.delete(key);
    }
  }
}

function clearAllSky() {
  for (const [, group] of skyCells) {
    scene.remove(group);
    group.traverse((o) => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
  }
  skyCells.clear();
}

/* ------------------------------------------------------------------ */
/*  Missile lowpoly + booster à propergol solide                       */
/* ------------------------------------------------------------------ */

function makeGlowTexture() {
  const size = 64;
  const canvas = document.createElement("canvas");
  canvas.width = size;
  canvas.height = size;
  const ctx = canvas.getContext("2d");
  const gradient = ctx.createRadialGradient(size / 2, size / 2, 0, size / 2, size / 2, size / 2);
  gradient.addColorStop(0, "rgba(255,255,255,1)");
  gradient.addColorStop(0.4, "rgba(255,200,100,0.8)");
  gradient.addColorStop(1, "rgba(255,120,30,0)");
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, size, size);
  return new THREE.CanvasTexture(canvas);
}

const ROCKET_NOZZLE_Z = -2.15;

function makeFinGeometry(span, rootChord, tipChord, sweep, thickness) {
  const shape = new THREE.Shape();
  shape.moveTo(0, 0);
  shape.lineTo(rootChord, 0);
  shape.lineTo(sweep + tipChord, span);
  shape.lineTo(sweep, span);
  shape.lineTo(0, 0);
  const geo = new THREE.ExtrudeGeometry(shape, { depth: thickness, bevelEnabled: false });
  geo.translate(0, 0, -thickness / 2);
  return geo;
}

function mountFin(geo, material, angle, radius, zOffset, scale = 1) {
  const mesh = new THREE.Mesh(geo, material);
  const eX = new THREE.Vector3(0, 0, -1); // longueur de corde vers l'arrière
  const eY = new THREE.Vector3(Math.cos(angle), Math.sin(angle), 0); // envergure radiale
  const eZ = new THREE.Vector3().crossVectors(eX, eY).normalize();
  mesh.quaternion.setFromRotationMatrix(new THREE.Matrix4().makeBasis(eX, eY, eZ));
  mesh.position.set(Math.cos(angle) * radius, Math.sin(angle) * radius, zOffset);
  mesh.scale.setScalar(scale);
  return mesh;
}

function buildRocket() {
  rocket = new THREE.Group();

  const noseMat = new THREE.MeshStandardMaterial({ color: 0x2b2f36, flatShading: true, metalness: 0.4, roughness: 0.45 });
  const bodyMat = new THREE.MeshStandardMaterial({ color: 0xe9ecef, flatShading: true, metalness: 0.2, roughness: 0.5 });
  const stripeMat = new THREE.MeshStandardMaterial({ color: 0xd93a2b, flatShading: true });
  const tailMat = new THREE.MeshStandardMaterial({ color: 0x3a3f47, flatShading: true, metalness: 0.5, roughness: 0.4 });
  const nozzleMat = new THREE.MeshStandardMaterial({ color: 0x18191c, flatShading: true, metalness: 0.6, roughness: 0.3 });
  const finMat = new THREE.MeshStandardMaterial({ color: 0x24262b, flatShading: true, metalness: 0.3, roughness: 0.55 });

  // Nez ogival (profil à plusieurs points, plus fin qu'un simple cône)
  const noseProfile = [
    new THREE.Vector2(0.42, 0),
    new THREE.Vector2(0.33, 0.55),
    new THREE.Vector2(0.15, 1.0),
    new THREE.Vector2(0.0, 1.3),
  ];
  const nose = new THREE.Mesh(new THREE.LatheGeometry(noseProfile, 8), noseMat);
  nose.rotation.x = Math.PI / 2;
  nose.position.z = 0.55;
  rocket.add(nose);

  const body = new THREE.Mesh(new THREE.CylinderGeometry(0.42, 0.42, 1.85, 8), bodyMat);
  body.rotation.x = Math.PI / 2;
  body.position.z = -0.4;
  rocket.add(body);

  const stripe = new THREE.Mesh(new THREE.CylinderGeometry(0.44, 0.44, 0.35, 8), stripeMat);
  stripe.rotation.x = Math.PI / 2;
  stripe.position.z = 0.32;
  rocket.add(stripe);

  // Jupe arrière effilée vers la tuyère
  const boatTail = new THREE.Mesh(new THREE.CylinderGeometry(0.42, 0.27, 0.55, 8), tailMat);
  boatTail.rotation.x = Math.PI / 2;
  boatTail.position.z = -1.6;
  rocket.add(boatTail);

  // Tuyère évasée du booster
  const nozzle = new THREE.Mesh(new THREE.CylinderGeometry(0.24, 0.46, 0.45, 8), nozzleMat);
  nozzle.rotation.x = Math.PI / 2;
  nozzle.position.z = ROCKET_NOZZLE_Z;
  rocket.add(nozzle);

  // Ailerons arrière en delta balayé, montage en X
  const tailFinGeo = makeFinGeometry(0.75, 1.0, 0.35, 0.5, 0.05);
  for (let i = 0; i < 4; i++) {
    const angle = Math.PI / 4 + (i / 4) * Math.PI * 2;
    rocket.add(mountFin(tailFinGeo, finMat, angle, 0.3, -1.55));
  }

  // Petits canards stabilisateurs près du nez
  const canardGeo = makeFinGeometry(0.4, 0.5, 0.2, 0.25, 0.04);
  for (let i = 0; i < 4; i++) {
    const angle = (i / 4) * Math.PI * 2;
    rocket.add(mountFin(canardGeo, finMat, angle, 0.43, 0.5, 0.85));
  }

  const flameGroup = new THREE.Group();
  flameGroup.position.z = ROCKET_NOZZLE_Z - 0.25;

  const coreMat = new THREE.MeshBasicMaterial({ color: 0xfff7d6, transparent: true, opacity: 0.95, blending: THREE.AdditiveBlending, depthWrite: false });
  const core = new THREE.Mesh(new THREE.ConeGeometry(0.22, 1.1, 6), coreMat);
  core.rotation.x = -Math.PI / 2;
  flameGroup.add(core);

  const midMat = new THREE.MeshBasicMaterial({ color: 0xff9a2e, transparent: true, opacity: 0.85, blending: THREE.AdditiveBlending, depthWrite: false });
  const mid = new THREE.Mesh(new THREE.ConeGeometry(0.4, 1.7, 7), midMat);
  mid.rotation.x = -Math.PI / 2;
  flameGroup.add(mid);

  const outerMat = new THREE.MeshBasicMaterial({ color: 0xe0451f, transparent: true, opacity: 0.55, blending: THREE.AdditiveBlending, depthWrite: false });
  const outer = new THREE.Mesh(new THREE.ConeGeometry(0.58, 2.3, 7), outerMat);
  outer.rotation.x = -Math.PI / 2;
  flameGroup.add(outer);

  rocket.add(flameGroup);

  flameLight = new THREE.PointLight(0xff9a3c, 0, 18, 2);
  flameLight.position.z = ROCKET_NOZZLE_Z - 0.5;
  rocket.add(flameLight);

  flameParts = { group: flameGroup, core, mid, outer };

  rocket.position.copy(rocketState.position);
  scene.add(rocket);
}

/* ------------------------------------------------------------------ */
/*  Cible (mode Cible) : un avion lowpoly volant en va-et-vient          */
/* ------------------------------------------------------------------ */

const PLANE_ALTITUDE = 140;
const PLANE_AMPLITUDE = 320;
const PLANE_SPEED = 0.22;
const TARGET_HIT_RADIUS = 6;

function buildPlane() {
  const group = new THREE.Group();

  const bodyMat = new THREE.MeshStandardMaterial({ color: 0xdfe2e6, flatShading: true, metalness: 0.3, roughness: 0.5 });
  const accentMat = new THREE.MeshStandardMaterial({ color: 0x2b5fd9, flatShading: true });

  const fuselage = new THREE.Mesh(new THREE.CylinderGeometry(0.55, 0.42, 5.2, 8), bodyMat);
  fuselage.rotation.x = Math.PI / 2;
  group.add(fuselage);

  const nose = new THREE.Mesh(new THREE.ConeGeometry(0.42, 1.1, 8), bodyMat);
  nose.rotation.x = Math.PI / 2;
  nose.position.z = 3.1;
  group.add(nose);

  const wing = new THREE.Mesh(new THREE.BoxGeometry(6.6, 0.14, 1.3), accentMat);
  wing.position.z = 0.1;
  group.add(wing);

  const tailWing = new THREE.Mesh(new THREE.BoxGeometry(2.4, 0.12, 0.7), accentMat);
  tailWing.position.set(0, 0.1, -2.3);
  group.add(tailWing);

  const fin = new THREE.Mesh(new THREE.BoxGeometry(0.12, 1.0, 0.9), bodyMat);
  fin.position.set(0, 0.6, -2.3);
  group.add(fin);

  return group;
}

function updatePlane(dt, elapsed) {
  if (!plane || !planeState || !planeState.alive) return;

  const t = elapsed * PLANE_SPEED;
  const x = planeState.center.x + Math.sin(t) * PLANE_AMPLITUDE;
  const z = planeState.center.z;
  plane.position.set(x, PLANE_ALTITUDE, z);
  // Vitesse analytique (dérivée de la trajectoire) : reprise telle quelle par
  // le missile au moment du largage quand il est porté par l'avion.
  planeState.velocity.set(Math.cos(t) * PLANE_AMPLITUDE * PLANE_SPEED, 0, 0);

  const movingPositive = Math.cos(t) >= 0;
  const targetHeading = movingPositive ? Math.PI / 2 : -Math.PI / 2;
  let diff = targetHeading - planeState.heading;
  diff = Math.atan2(Math.sin(diff), Math.cos(diff));
  planeState.heading += diff * Math.min(1, dt * 3);
  plane.rotation.y = planeState.heading;
  plane.rotation.z = Math.sin(t) * 0.15;
}

// Retourne la position/le statut de l'objet à percuter, selon la
// configuration choisie (l'avion ou le bateau peuvent être la cible).
function getTargetInfo() {
  if (gameMode !== "target") return null;
  if (targetConfig === "boatToPlane") {
    if (!plane || !planeState || !planeState.alive) return null;
    return { position: plane.position };
  }
  if (!launcher || !boatAlive) return null;
  return { position: launcher.position.clone().add(new THREE.Vector3(0, 1, 0)) };
}

function checkTargetHit() {
  if (!rocketState.launched) return;
  const info = getTargetInfo();
  if (!info) return;
  if (rocketState.position.distanceTo(info.position) < TARGET_HIT_RADIUS) {
    onTargetHit(info);
  }
}

function onTargetHit(info) {
  if (targetConfig === "boatToPlane") {
    planeState.alive = false;
    plane.visible = false;
  } else {
    boatAlive = false;
    launcher.visible = false;
  }
  const explosionPos = info.position.clone();
  spawnExplosion(explosionPos);
  spawnExplosion(explosionPos.clone().add(new THREE.Vector3((Math.random() - 0.5) * 2, (Math.random() - 0.5) * 2, (Math.random() - 0.5) * 2)));
  spawnFlash(explosionPos, 0xffcf7a, 7, 0.5);
  playImpactSound(32);
  triggerShake(14);
  flashToast("CIBLE DÉTRUITE !");
}

const LAUNCHER_PAD_HEIGHT = 0.4;
const LAUNCHER_TOWER_HEIGHT = 3.4;

function buildLauncher(x, z) {
  const group = new THREE.Group();
  const groundY = heightAt(x, z);

  const concreteMat = new THREE.MeshStandardMaterial({ color: 0x6b6d70, flatShading: true, roughness: 1 });
  const steelMat = new THREE.MeshStandardMaterial({ color: 0x3a3f47, flatShading: true, metalness: 0.5, roughness: 0.45 });
  const stripeMat = new THREE.MeshStandardMaterial({ color: 0xd93a2b, flatShading: true });

  const pad = new THREE.Mesh(new THREE.BoxGeometry(3.2, LAUNCHER_PAD_HEIGHT, 3.2), concreteMat);
  pad.position.y = LAUNCHER_PAD_HEIGHT / 2;
  group.add(pad);

  const half = 1.15;
  const corners = [
    [-half, -half], [half, -half], [half, half], [-half, half],
  ];
  for (const [cx, cz] of corners) {
    const beam = new THREE.Mesh(new THREE.BoxGeometry(0.16, LAUNCHER_TOWER_HEIGHT, 0.16), steelMat);
    beam.position.set(cx, LAUNCHER_PAD_HEIGHT + LAUNCHER_TOWER_HEIGHT / 2, cz);
    group.add(beam);
  }

  // Croisillons horizontaux, à deux hauteurs, avec une bande d'alerte rouge/blanc.
  for (const h of [1.1, 2.5]) {
    for (const [a, b] of [[corners[0], corners[1]], [corners[1], corners[2]], [corners[2], corners[3]], [corners[3], corners[0]]]) {
      const dx = b[0] - a[0], dz = b[1] - a[1];
      const len = Math.hypot(dx, dz);
      const brace = new THREE.Mesh(new THREE.BoxGeometry(len, 0.1, 0.1), stripeMat);
      brace.position.set((a[0] + b[0]) / 2, LAUNCHER_PAD_HEIGHT + h, (a[1] + b[1]) / 2);
      brace.rotation.y = Math.atan2(dz, dx);
      group.add(brace);
    }
  }

  group.position.set(x, groundY, z);
  scene.add(group);
  return group;
}

const WATER_LEVEL = -15;
const BOAT_DECK_HEIGHT = 2.0;

function buildBoat(x, z) {
  const group = new THREE.Group();

  const hullMat = new THREE.MeshStandardMaterial({ color: 0x8a5a3a, flatShading: true, roughness: 0.85 });
  const deckMat = new THREE.MeshStandardMaterial({ color: 0xc9b28a, flatShading: true, roughness: 0.9 });
  const cabinMat = new THREE.MeshStandardMaterial({ color: 0xe9ecef, flatShading: true, roughness: 0.5 });
  const stripeMat = new THREE.MeshStandardMaterial({ color: 0xd93a2b, flatShading: true });

  // Coque : silhouette vue de dessus (proue pointue), extrudée verticalement.
  const shape = new THREE.Shape();
  shape.moveTo(-4.6, -1.5);
  shape.lineTo(3.0, -1.5);
  shape.lineTo(4.8, 0);
  shape.lineTo(3.0, 1.5);
  shape.lineTo(-4.6, 1.5);
  shape.lineTo(-4.6, -1.5);
  const hullGeo = new THREE.ExtrudeGeometry(shape, { depth: 1.7, bevelEnabled: false });
  hullGeo.rotateX(-Math.PI / 2);
  const hull = new THREE.Mesh(hullGeo, hullMat);
  hull.position.y = -1.7;
  group.add(hull);

  const stripe = new THREE.Mesh(new THREE.BoxGeometry(9.6, 0.3, 3.05), stripeMat);
  stripe.position.y = -1.5;
  group.add(stripe);

  const deck = new THREE.Mesh(new THREE.BoxGeometry(8.6, 0.25, 2.8), deckMat);
  deck.position.y = 0.1;
  group.add(deck);

  const cabin = new THREE.Mesh(new THREE.BoxGeometry(2.0, 1.7, 2.3), cabinMat);
  cabin.position.set(-2.8, 1.1, 0);
  group.add(cabin);

  const mast = new THREE.Mesh(new THREE.CylinderGeometry(0.06, 0.06, 2.2, 6), hullMat);
  mast.position.set(-2.8, 2.9, 0);
  group.add(mast);

  group.position.set(x, WATER_LEVEL, z);
  scene.add(group);
  return group;
}

/* ------------------------------------------------------------------ */
/*  Particules : flamme + débris d'impact (pool partagé)               */
/* ------------------------------------------------------------------ */

function initSmoke() {
  smokeTexture = makeGlowTexture();
  for (let i = 0; i < SMOKE_COUNT; i++) {
    const material = new THREE.SpriteMaterial({
      map: smokeTexture,
      transparent: true,
      opacity: 0,
      depthWrite: false,
      blending: THREE.AdditiveBlending,
    });
    const sprite = new THREE.Sprite(material);
    sprite.visible = false;
    scene.add(sprite);
    smokePool.push({ sprite, velocity: new THREE.Vector3(), life: 0, maxLife: 1, active: false, startColor: new THREE.Color(), endColor: new THREE.Color() });
  }
}

let smokeCursor = 0;
let smokeEmitAccum = 0;

function emitParticle(origin, velocity, opts) {
  const p = smokePool[smokeCursor];
  smokeCursor = (smokeCursor + 1) % SMOKE_COUNT;

  p.active = true;
  p.life = 0;
  p.maxLife = opts.maxLife;
  p.sprite.position.copy(origin);
  p.sprite.scale.setScalar(opts.startScale);
  p.startScale = opts.startScale;
  p.endScale = opts.endScale;
  p.startColor.set(opts.startColor);
  p.endColor.set(opts.endColor);
  p.sprite.material.opacity = opts.startOpacity;
  p.sprite.material.color.copy(p.startColor);
  p.sprite.visible = true;
  p.velocity.copy(velocity);
  p.drag = opts.drag ?? 0.94;
  p.gravity = opts.gravity ?? 0;
}

function updateSmoke(dt) {
  for (const p of smokePool) {
    if (!p.active) continue;
    p.life += dt;
    const t = p.life / p.maxLife;
    if (t >= 1) {
      p.active = false;
      p.sprite.visible = false;
      continue;
    }
    p.velocity.y -= p.gravity * dt;
    p.sprite.position.addScaledVector(p.velocity, dt);
    p.velocity.multiplyScalar(p.drag);
    p.sprite.scale.setScalar(THREE.MathUtils.lerp(p.startScale, p.endScale, t));
    p.sprite.material.opacity = (1 - t);
    p.sprite.material.color.copy(p.startColor).lerp(p.endColor, t);
  }
}

function emitThrusterSmoke(origin, backward) {
  const spread = 0.6;
  const v = backward.clone().multiplyScalar(6 + Math.random() * 3);
  v.x += (Math.random() - 0.5) * spread;
  v.y += (Math.random() - 0.5) * spread + 0.5;
  v.z += (Math.random() - 0.5) * spread;
  emitParticle(origin, v, {
    maxLife: 0.55 + Math.random() * 0.45,
    startScale: 0.7 + Math.random() * 0.5,
    endScale: 2.6,
    startOpacity: 0.9,
    startColor: 0xffcf7a,
    endColor: 0x7a6a5a,
    drag: 0.94,
    gravity: -0.5,
  });
}

function spawnImpactBurst(position, normal, impactSpeed) {
  const count = THREE.MathUtils.clamp(Math.round(impactSpeed * 1.2), 10, 40);
  for (let i = 0; i < count; i++) {
    const dir = normal.clone()
      .addScaledVector(new THREE.Vector3(Math.random() - 0.5, Math.random() - 0.5, Math.random() - 0.5), 0.9)
      .normalize();
    const speed = impactSpeed * (0.3 + Math.random() * 0.6);
    emitParticle(position, dir.multiplyScalar(speed), {
      maxLife: 0.5 + Math.random() * 0.6,
      startScale: 0.5 + Math.random() * 0.6,
      endScale: 0.2,
      startOpacity: 1,
      startColor: 0xffe1a3,
      endColor: 0x5a4a3a,
      drag: 0.9,
      gravity: 9,
    });
  }
}

function spawnLaunchSmoke() {
  const origin = rocketState.position.clone().addScaledVector(new THREE.Vector3(0, -1, 0), 1.4);
  for (let i = 0; i < 36; i++) {
    const spread = new THREE.Vector3((Math.random() - 0.5) * 6, Math.random() * 2, (Math.random() - 0.5) * 6);
    emitParticle(origin, spread, {
      maxLife: 0.7 + Math.random() * 0.6,
      startScale: 0.8 + Math.random() * 0.8,
      endScale: 3.2,
      startOpacity: 0.9,
      startColor: 0xffe1a3,
      endColor: 0x8a8a86,
      drag: 0.92,
      gravity: -1.2,
    });
  }
}

function spawnExplosion(position) {
  for (let i = 0; i < 60; i++) {
    const dir = new THREE.Vector3(Math.random() - 0.5, Math.random() - 0.5, Math.random() - 0.5).normalize();
    const speed = 6 + Math.random() * 18;
    emitParticle(position, dir.multiplyScalar(speed), {
      maxLife: 0.6 + Math.random() * 0.7,
      startScale: 0.7 + Math.random() * 1.1,
      endScale: 3.4,
      startOpacity: 1,
      startColor: 0xfff2b0,
      endColor: 0x4a423a,
      drag: 0.9,
      gravity: 4,
    });
  }
}

// Éclair lumineux bref (flash d'explosion), géré via une petite liste de
// lumières temporaires qui s'éteignent puis se retirent de la scène.
const flashLights = [];

function spawnFlash(position, color, intensity, maxLife) {
  const light = new THREE.PointLight(color, intensity, 70, 2);
  light.position.copy(position);
  scene.add(light);
  flashLights.push({ light, life: 0, maxLife, baseIntensity: intensity });
}

function updateFlashLights(dt) {
  for (let i = flashLights.length - 1; i >= 0; i--) {
    const f = flashLights[i];
    f.life += dt;
    const t = f.life / f.maxLife;
    if (t >= 1) {
      scene.remove(f.light);
      flashLights.splice(i, 1);
      continue;
    }
    f.light.intensity = f.baseIntensity * (1 - t);
  }
}

/* ------------------------------------------------------------------ */
/*  Toast / secousse caméra                                             */
/* ------------------------------------------------------------------ */

const toastEl = document.getElementById("toast");
function flashToast(text) {
  toastEl.textContent = text;
  toastEl.classList.remove("show");
  void toastEl.offsetWidth;
  toastEl.classList.add("show");
}

const launchHintEl = document.getElementById("launchHint");
function updateLaunchHint() {
  launchHintEl.classList.toggle("hidden", rocketState.launched);
}

function triggerShake(amount) {
  cameraShake.intensity = Math.min(2.4, cameraShake.intensity + amount * 0.05);
}

/* ------------------------------------------------------------------ */
/*  Son (synthèse procédurale via Web Audio, aucun fichier externe)     */
/* ------------------------------------------------------------------ */

let audioCtx = null;
let masterGain = null;
let thrusterGain, thrusterFilter, thrusterFilter2, rumbleGain;

function createNoiseBuffer(seconds, color = "white") {
  const length = Math.floor(audioCtx.sampleRate * seconds);
  const buffer = audioCtx.createBuffer(1, length, audioCtx.sampleRate);
  const data = buffer.getChannelData(0);

  if (color === "brown") {
    // Bruit brownien (marche aléatoire) : beaucoup plus doux et grave que le
    // bruit blanc, sans son énergie stridente dans les aigus — idéal pour un
    // grondement de moteur au lieu d'un bruit de "friture".
    let last = 0;
    for (let i = 0; i < length; i++) {
      const white = Math.random() * 2 - 1;
      last = (last + white * 0.02) / 1.02;
      data[i] = last * 3.2;
    }
  } else {
    for (let i = 0; i < length; i++) data[i] = Math.random() * 2 - 1;
  }

  // Fondu de raccord en fin de buffer pour un bouclage sans clic audible.
  const fadeLen = Math.floor(length * 0.05);
  for (let i = 0; i < fadeLen; i++) {
    const t = i / fadeLen;
    const idxEnd = length - fadeLen + i;
    data[idxEnd] = data[idxEnd] * (1 - t) + data[i] * t;
  }

  return buffer;
}

function ensureAudio() {
  if (audioCtx) {
    if (audioCtx.state === "suspended") audioCtx.resume().then(updateSoundButton);
    updateSoundButton();
    return;
  }
  try {
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();

    masterGain = audioCtx.createGain();
    masterGain.gain.value = 0.5;

    // Compresseur final : évite l'écrêtage numérique (le "grésillement") quand
    // le moteur et un impact jouent en même temps et que les niveaux s'additionnent.
    const limiter = audioCtx.createDynamicsCompressor();
    limiter.threshold.value = -12;
    limiter.knee.value = 18;
    limiter.ratio.value = 12;
    limiter.attack.value = 0.003;
    limiter.release.value = 0.15;

    masterGain.connect(limiter);
    limiter.connect(audioCtx.destination);

    // Souffle du booster : bruit brownien (doux, grave) filtré en boucle,
    // dont le volume et le timbre suivent l'intensité de la flamme. Deux
    // filtres passe-bas en série pour une coupure plus franche des aigus
    // (évite le côté "friture" d'un simple bruit blanc filtré une fois).
    const noiseSource = audioCtx.createBufferSource();
    noiseSource.buffer = createNoiseBuffer(3, "brown");
    noiseSource.loop = true;
    thrusterFilter = audioCtx.createBiquadFilter();
    thrusterFilter.type = "lowpass";
    thrusterFilter.frequency.value = 300;
    thrusterFilter.Q.value = 0.3;
    thrusterFilter2 = audioCtx.createBiquadFilter();
    thrusterFilter2.type = "lowpass";
    thrusterFilter2.frequency.value = 500;
    thrusterFilter2.Q.value = 0.3;
    thrusterGain = audioCtx.createGain();
    thrusterGain.gain.value = 0;
    noiseSource.connect(thrusterFilter);
    thrusterFilter.connect(thrusterFilter2);
    thrusterFilter2.connect(thrusterGain);
    thrusterGain.connect(masterGain);
    noiseSource.start();

    // Grondement grave superposé (triangle, plus doux qu'une dent de scie),
    // pour donner du corps au son du propergol solide sans agressivité.
    const rumble = audioCtx.createOscillator();
    rumble.type = "triangle";
    rumble.frequency.value = 45;
    rumbleGain = audioCtx.createGain();
    rumbleGain.gain.value = 0;
    rumble.connect(rumbleGain);
    rumbleGain.connect(masterGain);
    rumble.start();

    audioCtx.resume().then(updateSoundButton);
  } catch (err) {
    console.error("Impossible d'initialiser l'audio :", err);
  }
  updateSoundButton();
}

function updateSoundButton() {
  const btn = document.getElementById("soundButton");
  if (!btn) return;
  const running = !!audioCtx && audioCtx.state === "running";
  btn.textContent = running ? "🔊 Son activé" : "🔇 Activer le son";
  btn.classList.toggle("on", running);
}

function updateThrusterSound(intensity) {
  if (!audioCtx) return;
  const now = audioCtx.currentTime;
  thrusterGain.gain.setTargetAtTime(intensity * 0.5, now, 0.05);
  thrusterFilter.frequency.setTargetAtTime(280 + intensity * 700, now, 0.1);
  thrusterFilter2.frequency.setTargetAtTime(450 + intensity * 900, now, 0.1);
  rumbleGain.gain.setTargetAtTime(intensity * 0.22, now, 0.08);
}

let lastImpactSoundTime = -Infinity;

function playImpactSound(impactSpeed) {
  if (!audioCtx) return;
  const now = audioCtx.currentTime;
  // Évite l'empilement de sons (et le grésillement qui en résulte) quand
  // plusieurs petits rebonds se succèdent très rapidement.
  if (now - lastImpactSoundTime < 0.09) return;
  lastImpactSoundTime = now;
  const strength = THREE.MathUtils.clamp(impactSpeed / 30, 0.2, 1);

  const thump = audioCtx.createOscillator();
  thump.type = "sine";
  thump.frequency.setValueAtTime(160, now);
  thump.frequency.exponentialRampToValueAtTime(35, now + 0.18);
  const thumpGain = audioCtx.createGain();
  thumpGain.gain.setValueAtTime(strength * 0.7, now);
  thumpGain.gain.exponentialRampToValueAtTime(0.001, now + 0.28);
  thump.connect(thumpGain);
  thumpGain.connect(masterGain);
  thump.start(now);
  thump.stop(now + 0.3);

  const crunchSource = audioCtx.createBufferSource();
  crunchSource.buffer = createNoiseBuffer(0.3);
  const crunchFilter = audioCtx.createBiquadFilter();
  crunchFilter.type = "bandpass";
  crunchFilter.frequency.value = 900;
  crunchFilter.Q.value = 0.6;
  const crunchGain = audioCtx.createGain();
  crunchGain.gain.setValueAtTime(strength * 0.5, now);
  crunchGain.gain.exponentialRampToValueAtTime(0.001, now + 0.22);
  crunchSource.connect(crunchFilter);
  crunchFilter.connect(crunchGain);
  crunchGain.connect(masterGain);
  crunchSource.start(now);
  crunchSource.stop(now + 0.3);
}

function playRegenerateSound() {
  if (!audioCtx) return;
  const now = audioCtx.currentTime;
  const sweep = audioCtx.createOscillator();
  sweep.type = "triangle";
  sweep.frequency.setValueAtTime(220, now);
  sweep.frequency.exponentialRampToValueAtTime(660, now + 0.25);
  const sweepGain = audioCtx.createGain();
  sweepGain.gain.setValueAtTime(0.25, now);
  sweepGain.gain.exponentialRampToValueAtTime(0.001, now + 0.3);
  sweep.connect(sweepGain);
  sweepGain.connect(masterGain);
  sweep.start(now);
  sweep.stop(now + 0.32);
}

function playLaunchSound() {
  if (!audioCtx) return;
  const now = audioCtx.currentTime;

  // Coup de bélier grave (l'impulsion de lancement).
  const thump = audioCtx.createOscillator();
  thump.type = "sine";
  thump.frequency.setValueAtTime(90, now);
  thump.frequency.exponentialRampToValueAtTime(30, now + 0.35);
  const thumpGain = audioCtx.createGain();
  thumpGain.gain.setValueAtTime(0.8, now);
  thumpGain.gain.exponentialRampToValueAtTime(0.001, now + 0.45);
  thump.connect(thumpGain);
  thumpGain.connect(masterGain);
  thump.start(now);
  thump.stop(now + 0.5);

  // Souffle d'éjection : bruit brownien filtré, montée puis chute rapide.
  const blastSource = audioCtx.createBufferSource();
  blastSource.buffer = createNoiseBuffer(0.6, "brown");
  const blastFilter = audioCtx.createBiquadFilter();
  blastFilter.type = "lowpass";
  blastFilter.frequency.setValueAtTime(200, now);
  blastFilter.frequency.linearRampToValueAtTime(1400, now + 0.15);
  blastFilter.frequency.exponentialRampToValueAtTime(150, now + 0.6);
  const blastGain = audioCtx.createGain();
  blastGain.gain.setValueAtTime(0.7, now);
  blastGain.gain.exponentialRampToValueAtTime(0.001, now + 0.55);
  blastSource.connect(blastFilter);
  blastFilter.connect(blastGain);
  blastGain.connect(masterGain);
  blastSource.start(now);
  blastSource.stop(now + 0.6);
}

/* ------------------------------------------------------------------ */
/*  Scène / rendu                                                      */
/* ------------------------------------------------------------------ */

function init() {
  scene = new THREE.Scene();
  scene.background = new THREE.Color(0x9fd3e8);
  scene.fog = new THREE.Fog(0x9fd3e8, 220, 620);

  camera = new THREE.PerspectiveCamera(65, window.innerWidth / window.innerHeight, 0.1, 2000);

  renderer = new THREE.WebGLRenderer({ canvas: document.getElementById("scene"), antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setSize(window.innerWidth, window.innerHeight);

  const hemi = new THREE.HemisphereLight(0xbfe3ff, 0x3a3a2a, 0.9);
  scene.add(hemi);

  const sun = new THREE.DirectionalLight(0xfff4d6, 1.1);
  sun.position.set(150, 200, 100);
  scene.add(sun);

  terrainMaterial = new THREE.MeshStandardMaterial({
    vertexColors: true,
    flatShading: true,
    roughness: 1,
    metalness: 0,
  });

  const waterGeo = new THREE.PlaneGeometry(6000, 6000);
  waterGeo.rotateX(-Math.PI / 2);
  const waterMat = new THREE.MeshStandardMaterial({
    color: 0x2a6f8f,
    transparent: true,
    opacity: 0.75,
    roughness: 0.3,
    flatShading: true,
  });
  water = new THREE.Mesh(waterGeo, waterMat);
  water.position.y = WATER_LEVEL;
  scene.add(water);

  initSmoke();

  window.addEventListener("resize", onResize);
  window.addEventListener("keydown", (e) => {
    if (e.code === "Space") e.preventDefault();
    ensureAudio(); // le son ne peut démarrer qu'après un geste de l'utilisateur
    keys[e.code] = true;
    if (menuOpen) return;
    if (e.code === "KeyR") restart();
    if (e.code === "KeyL") launchRocket();
    if (e.code === "KeyM") showMenu();
  });
  window.addEventListener("keyup", (e) => { keys[e.code] = false; });

  const soundButton = document.getElementById("soundButton");
  soundButton.addEventListener("click", ensureAudio);
  // Un clic direct est le geste le plus fiable pour débloquer l'audio sur tous
  // les navigateurs ; on tente aussi sur le tout premier clic n'importe où.
  window.addEventListener("pointerdown", ensureAudio, { once: true });

  // Balayage de l'environnement uniquement au clic-glissé : le bouton doit
  // être maintenu enfoncé, sinon la vue revient se centrer sur la cible.
  window.addEventListener("mousedown", (e) => {
    if (e.button !== 0) return;
    dragLooking = true;
    lastDragX = e.clientX;
    lastDragY = e.clientY;
    mouseLook.x = 0;
    mouseLook.y = 0;
  });
  window.addEventListener("mouseup", () => { dragLooking = false; });
  window.addEventListener("mouseleave", () => { dragLooking = false; });
  window.addEventListener("mousemove", (e) => {
    if (!dragLooking) return;
    const dx = e.clientX - lastDragX;
    const dy = e.clientY - lastDragY;
    lastDragX = e.clientX;
    lastDragY = e.clientY;
    mouseLook.x = THREE.MathUtils.clamp(mouseLook.x + dx * DRAG_LOOK_SENSITIVITY, -1, 1);
    mouseLook.y = THREE.MathUtils.clamp(mouseLook.y + dy * DRAG_LOOK_SENSITIVITY, -1, 1);
  });

  document.getElementById("modeFreeBtn").addEventListener("click", () => startGame("free"));
  document.getElementById("modeTargetBtn").addEventListener("click", showTargetConfigMenu);
  document.getElementById("configBoatToPlaneBtn").addEventListener("click", () => startGame("target", "boatToPlane"));
  document.getElementById("configPlaneToBoatBtn").addEventListener("click", () => startGame("target", "planeToBoat"));
  document.getElementById("backToMainMenuBtn").addEventListener("click", showMainMenuGrid);
  document.getElementById("menuButton").addEventListener("click", showMenu);

  animate();
}

function showMenu() {
  menuOpen = true;
  document.getElementById("menuOverlay").classList.remove("hidden");
  showMainMenuGrid();
}

function showMainMenuGrid() {
  document.getElementById("menuSubtitleText").textContent = "Choisis un mode de jeu";
  document.getElementById("modeGridMain").classList.remove("hidden");
  document.getElementById("modeGridTarget").classList.add("hidden");
  document.getElementById("backToMainMenuBtn").classList.add("hidden");
}

function showTargetConfigMenu() {
  document.getElementById("menuSubtitleText").textContent = "Choisis ton point de départ et ta cible";
  document.getElementById("modeGridMain").classList.add("hidden");
  document.getElementById("modeGridTarget").classList.remove("hidden");
  document.getElementById("backToMainMenuBtn").classList.remove("hidden");
}

function startGame(mode, config = "boatToPlane") {
  gameMode = mode;
  targetConfig = config;
  menuOpen = false;
  document.getElementById("menuOverlay").classList.add("hidden");
  restart();
}

function restart() {
  playRegenerateSound();
  worldSeed = (Math.random() * 1e9) | 0;
  noise2D = makeNoise2D(worldSeed);
  clearAllChunks();
  clearAllSky();

  if (rocket) {
    scene.remove(rocket);
    rocket.traverse((o) => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
  }
  if (launcher) {
    scene.remove(launcher);
    launcher.traverse((o) => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
  }
  if (plane) {
    scene.remove(plane);
    plane.traverse((o) => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
    plane = null;
  }
  planeState = null;

  boatAlive = true;
  attachedToPlane = gameMode === "target" && targetConfig === "planeToBoat";

  let originX = 0, originZ = 0;
  let padTopY;
  if (gameMode === "target") {
    originX = (Math.random() - 0.5) * 300;
    originZ = (Math.random() - 0.5) * 300;
    // Rayon volontairement bien au-delà de la distance du brouillard (620) :
    // aucune terre ne peut donc jamais devenir visible à l'horizon, même en
    // levant la vue depuis le bateau.
    oceanSafeZone = { x: originX, z: originZ, radius: 800 };
    padTopY = WATER_LEVEL + BOAT_DECK_HEIGHT;
  } else {
    oceanSafeZone = null;
    padTopY = heightAt(originX, originZ) + LAUNCHER_PAD_HEIGHT;
  }

  rocketState.velocity.set(0, 0, 0);
  rocketState.heading = 0;
  rocketState.pitchAngle = Math.PI / 2;
  rocketState.roll = 0;
  rocketState.yawRate = 0;
  rocketState.pitchRate = 0;
  rocketState.thrustOn = false;
  rocketState.flameIntensity = 0;
  rocketState.grounded = false;
  rocketState.launched = false;

  if (gameMode === "target") {
    launcher = buildBoat(originX, originZ);
    launcher.visible = true;
    plane = buildPlane();
    scene.add(plane);
    planeState = { center: new THREE.Vector3(originX, 0, originZ), heading: Math.PI / 2, alive: true, velocity: new THREE.Vector3() };
    updatePlane(0, clock.getElapsedTime());
    plane.visible = true;

    if (attachedToPlane) {
      // Départ : accroché sous l'avion porteur. Le missile suit sa position
      // et son cap tant qu'il n'est pas largué (touche L).
      rocketState.position.copy(plane.position);
      rocketState.heading = planeState.heading;
      rocketState.pitchAngle = 0;
      flashToast("Fonce sur le bateau !");
    } else {
      const startY = padTopY + 1.7;
      rocketState.position.set(originX, startY, originZ);
      flashToast("Fonce sur l'avion !");
    }
  } else {
    launcher = buildLauncher(originX, originZ);
    const startY = padTopY + 1.7;
    rocketState.position.set(originX, startY, originZ);
  }

  rocketState.orientation.copy(headingPitchOrientation(rocketState.heading, rocketState.pitchAngle));
  buildRocket();

  cameraRig.yaw = rocketState.heading;
  cameraRig.position.copy(rocketState.position).addScaledVector(
    new THREE.Vector3(-Math.sin(cameraRig.yaw), 0, -Math.cos(cameraRig.yaw)), CAMERA_DISTANCE_BACK
  ).add(new THREE.Vector3(0, CAMERA_HEIGHT_ABOVE, 0));
  cameraRig.lookTarget.copy(rocketState.position);

  updateChunks(originX, originZ);
  updateSkyCells(originX, originZ);
  sinceChunkUpdate = 0;
  updateLaunchHint();
}

function onResize() {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
}

/* ------------------------------------------------------------------ */
/*  Physique du missile                                                 */
/* ------------------------------------------------------------------ */

const YAW_ANGULAR_ACCEL = 2.6;
const PITCH_ANGULAR_ACCEL = 2.0;
const ANGULAR_DAMPING = 3.2; // freinage doux pendant l'appui (garde de l'inertie, sensation de poids)
const ANGULAR_DAMPING_RELEASE = 11; // dès qu'on lâche la touche, on "recalibre" : la rotation résiduelle est tuée rapidement au lieu de continuer sur l'inertie

const AXIS_X = new THREE.Vector3(1, 0, 0);
const AXIS_Y = new THREE.Vector3(0, 1, 0);
const AXIS_Z = new THREE.Vector3(0, 0, 1);
const FORWARD_LOCAL = new THREE.Vector3(0, 0, 1);

// Construit l'orientation à partir d'un cap (lacet, autour de l'axe monde Y)
// et d'un tangage libre (autour de l'axe "droite" dérivé uniquement de ce
// cap). Comme l'axe de tangage ne dépend jamais du tangage lui-même, monter,
// descendre, tourner à gauche ou à droite reste cohérent à n'importe quelle
// inclinaison — y compris à la verticale pure, juste après un décollage.
function headingPitchOrientation(heading, pitchAngle) {
  const headingQuat = new THREE.Quaternion().setFromAxisAngle(AXIS_Y, heading);
  const rightAxis = AXIS_X.clone().applyQuaternion(headingQuat);
  const pitchQuat = new THREE.Quaternion().setFromAxisAngle(rightAxis, -pitchAngle);
  return pitchQuat.multiply(headingQuat);
}

const THRUST_ACCEL = 62;
const GRAVITY = 18;
const QUADRATIC_DRAG = 0.0022;
const LATERAL_DAMPING = 0.9; // ne s'applique que sous poussée : c'est le vecteur de poussée qui redirige la trajectoire, pas l'orientation seule

const RESTITUTION = 0.42;
const BOUNCE_THRESHOLD = 6;
const REST_FRICTION = 0.86;
const GROUND_OFFSET = 0.5;

const LAUNCH_IMPULSE = 24;

const forwardVec = new THREE.Vector3();

const PLANE_RELEASE_BOOST = 10;

function launchRocket() {
  if (rocketState.launched) return;
  rocketState.launched = true;
  if (attachedToPlane) {
    // Largué depuis l'avion : reprend sa vitesse de déplacement, plus une
    // petite impulsion vers l'avant (pas de poussée verticale ici).
    const forward = FORWARD_LOCAL.clone().applyQuaternion(rocketState.orientation);
    rocketState.velocity.copy(planeState.velocity).addScaledVector(forward, PLANE_RELEASE_BOOST);
  } else {
    rocketState.velocity.set(0, LAUNCH_IMPULSE, 0);
  }
  playLaunchSound();
  spawnLaunchSmoke();
  triggerShake(4);
  updateLaunchHint();
}

function updateRocket(dt, elapsed) {
  const yawInput = (keys["ArrowLeft"] || keys["KeyQ"] ? 1 : 0) - (keys["ArrowRight"] || keys["KeyD"] ? 1 : 0);
  const pitchInput = (keys["ArrowUp"] || keys["KeyZ"] || keys["KeyW"] ? 1 : 0) - (keys["ArrowDown"] || keys["KeyS"] ? 1 : 0);

  // --- Avant le lancement : soit sur la rampe (on peut viser au lacet), soit
  // accroché sous l'avion porteur (on suit sa position/son cap). Rien ne
  // bouge sous contrôle joueur avant d'appuyer sur L. Pas de gravité, pas de
  // moteur, pas de tangage.
  if (!rocketState.launched) {
    if (attachedToPlane && plane) {
      rocketState.position.copy(plane.position).add(new THREE.Vector3(0, -1.2, 0));
      rocketState.heading = planeState.heading;
    } else {
      rocketState.yawRate += yawInput * YAW_ANGULAR_ACCEL * dt;
      rocketState.yawRate *= Math.max(0, 1 - (yawInput ? ANGULAR_DAMPING : ANGULAR_DAMPING_RELEASE) * dt);
      rocketState.heading += rocketState.yawRate * dt;
    }
    rocketState.pitchRate = 0;
    rocketState.thrustOn = false;
    rocketState.flameIntensity = 0;
    rocketState.orientation.copy(headingPitchOrientation(rocketState.heading, rocketState.pitchAngle));

    rocket.position.copy(rocketState.position);
    rocket.quaternion.copy(rocketState.orientation);
    flameParts.group.visible = false;
    flameLight.intensity = 0;
    updateThrusterSound(0);
    updateHud(0, rocketState.position.y - heightAt(rocketState.position.x, rocketState.position.z));
    return;
  }

  // --- Rotation avec inertie angulaire, cap + tangage façon avion (aucune
  // borne sur le tangage : les loopings complets sont possibles). Le cap
  // tourne toujours autour de l'axe vertical du monde et le tangage autour
  // de l'axe "droite" dérivé de ce cap : haut/bas et gauche/droite restent
  // donc cohérents à n'importe quelle inclinaison, même à la verticale. ---
  rocketState.yawRate += yawInput * YAW_ANGULAR_ACCEL * dt;
  rocketState.pitchRate += pitchInput * PITCH_ANGULAR_ACCEL * dt;
  // Freinage doux tant qu'on tient la touche (inertie), mais dès qu'on la
  // relâche on "recalibre" en tuant vite la rotation résiduelle — sinon un
  // flip provoqué en tenant trop longtemps continuerait de tourner tout seul.
  rocketState.yawRate *= Math.max(0, 1 - (yawInput ? ANGULAR_DAMPING : ANGULAR_DAMPING_RELEASE) * dt);
  rocketState.pitchRate *= Math.max(0, 1 - (pitchInput ? ANGULAR_DAMPING : ANGULAR_DAMPING_RELEASE) * dt);

  rocketState.heading += rocketState.yawRate * dt;
  rocketState.pitchAngle += rocketState.pitchRate * dt;
  rocketState.orientation.copy(headingPitchOrientation(rocketState.heading, rocketState.pitchAngle));

  rocketState.thrustOn = !!keys["Space"];

  forwardVec.copy(FORWARD_LOCAL).applyQuaternion(rocketState.orientation);

  // --- Forces ---
  if (rocketState.thrustOn) {
    rocketState.velocity.addScaledVector(forwardVec, THRUST_ACCEL * dt);
  }
  rocketState.velocity.y -= GRAVITY * dt;

  const speed = rocketState.velocity.length();
  if (speed > 0.001) {
    const dragMag = QUADRATIC_DRAG * speed * speed;
    rocketState.velocity.addScaledVector(rocketState.velocity, -(dragMag * dt) / speed);
  }

  // Sous poussée seulement, le vecteur de poussée "carve" progressivement la trajectoire
  // vers le nez (comme un vrai empennage sous flux d'air propulsé). Sans poussée, la
  // vitesse reste purement balistique : tourner ou flipper le nez ne dévie pas la
  // trajectoire, elle continue (presque) tout droit sous l'effet de son inertie propre.
  if (rocketState.thrustOn) {
    const vAlong = rocketState.velocity.dot(forwardVec);
    const vAlongVec = forwardVec.clone().multiplyScalar(vAlong);
    const vLateral = rocketState.velocity.clone().sub(vAlongVec);
    vLateral.multiplyScalar(Math.max(0, 1 - LATERAL_DAMPING * dt));
    rocketState.velocity.copy(vAlongVec.add(vLateral));
  }

  rocketState.position.addScaledVector(rocketState.velocity, dt);

  // --- Collision / rebond sur le sol ---
  handleGroundCollision(dt);

  // --- Plafond doux (au lieu d'un crash) ---
  if (rocketState.position.y > 420) {
    rocketState.velocity.y -= 40 * dt;
  }

  rocket.position.copy(rocketState.position);

  // Roulis purement cosmétique (retour visuel dans les virages), appliqué en
  // repère local par-dessus l'orientation réelle — n'affecte jamais la physique.
  const targetBank = THREE.MathUtils.clamp(-rocketState.yawRate * 0.35, -0.8, 0.8);
  rocketState.roll = THREE.MathUtils.lerp(rocketState.roll, targetBank, 1 - Math.pow(0.001, dt));
  const bankQuat = new THREE.Quaternion().setFromAxisAngle(AXIS_Z, rocketState.roll);
  rocket.quaternion.copy(rocketState.orientation).multiply(bankQuat);

  updateFlame(dt, elapsed);

  updateHud(rocketState.velocity.length(), rocketState.position.y - heightAt(rocketState.position.x, rocketState.position.z));
}

function handleGroundCollision() {
  const pos = rocketState.position;
  const groundY = heightAt(pos.x, pos.z);
  const penetration = groundY + GROUND_OFFSET - pos.y;

  if (penetration <= 0) {
    rocketState.grounded = false;
    return;
  }

  const normal = terrainNormalAt(pos.x, pos.z);
  pos.addScaledVector(normal, penetration);

  const vDotN = rocketState.velocity.dot(normal);
  if (vDotN < 0) {
    const impactSpeed = -vDotN;
    const vNormal = normal.clone().multiplyScalar(vDotN);
    const vTangent = rocketState.velocity.clone().sub(vNormal);

    if (impactSpeed > BOUNCE_THRESHOLD) {
      rocketState.velocity.copy(vTangent.multiplyScalar(0.7)).addScaledVector(normal, -vDotN * RESTITUTION);
      spawnImpactBurst(pos.clone().addScaledVector(normal, 0.3), normal, impactSpeed);
      triggerShake(impactSpeed);
      playImpactSound(impactSpeed);
      flashToast(impactSpeed > 22 ? "GROS IMPACT !" : "IMPACT !");
    } else {
      rocketState.velocity.copy(vTangent.multiplyScalar(REST_FRICTION));
    }
  }
  rocketState.grounded = true;
}

function updateFlame(dt, elapsed) {
  const target = rocketState.thrustOn ? 1 : 0;
  rocketState.flameIntensity = THREE.MathUtils.lerp(rocketState.flameIntensity, target, 1 - Math.pow(0.00002, dt));
  const intensity = rocketState.flameIntensity;

  if (intensity > 0.01) {
    flameParts.group.visible = true;
    const flicker = 0.85 + 0.1 * Math.sin(elapsed * 55) + 0.08 * Math.sin(elapsed * 91 + 1.7) + (Math.random() - 0.5) * 0.12;
    const lenFactor = intensity * Math.max(0.5, flicker);
    flameParts.core.scale.set(1, lenFactor * 1.1, 1);
    flameParts.mid.scale.set(1, lenFactor, 1);
    flameParts.outer.scale.set(1, lenFactor * 0.85, 1);
    flameParts.core.material.opacity = 0.95 * intensity;
    flameParts.mid.material.opacity = 0.85 * intensity;
    flameParts.outer.material.opacity = 0.5 * intensity;
    flameLight.intensity = intensity * (2.4 + Math.random() * 1.2);
  } else {
    flameParts.group.visible = false;
    flameLight.intensity = 0;
  }
  updateThrusterSound(intensity);

  if (rocketState.thrustOn) {
    const backward = forwardVec.clone().multiplyScalar(-1);
    const tipLocal = new THREE.Vector3(0, 0, ROCKET_NOZZLE_Z - 0.9 - Math.random() * 0.6);
    const tipWorld = tipLocal
      .applyQuaternion(rocketState.orientation)
      .add(rocketState.position);
    smokeEmitAccum += dt;
    const emitInterval = 0.02;
    while (smokeEmitAccum > emitInterval) {
      emitThrusterSmoke(tipWorld, backward);
      smokeEmitAccum -= emitInterval;
    }
  }
}

/* ------------------------------------------------------------------ */
/*  Caméra de poursuite                                                 */
/* ------------------------------------------------------------------ */

const CAMERA_TURN_SMOOTH = 3.2; // plus petit = caméra plus "molle" derrière les manœuvres
const CAMERA_DISTANCE_BACK = 15; // recul horizontal derrière le missile
const CAMERA_HEIGHT_ABOVE = 11; // hauteur au-dessus du missile (vue en surplomb)
const MOUSE_LOOK_YAW = 1.1; // amplitude max (rad) du balayage horizontal à la souris
const MOUSE_LOOK_PITCH = 0.7; // amplitude max (rad) du balayage vertical à la souris
const smoothedMouseLook = { x: 0, y: 0 };

function updateCamera(dt) {
  // Vue en surplomb à angle fixe : la caméra ne suit que le cap (lacet) du
  // déplacement réel, jamais le tangage/roulis du missile — elle reste donc
  // toujours au-dessus, inclinée vers le bas, sans jamais piquer ou se
  // retourner avec les manœuvres.
  const speed = rocketState.velocity.length();
  let targetYaw = cameraRig.yaw;
  if (speed > 3) {
    const dir = rocketState.velocity;
    const horizontal = Math.hypot(dir.x, dir.z);
    // Quand la trajectoire devient quasi verticale, la composante horizontale
    // s'effondre et atan2 devient instable : on garde alors le dernier cap connu
    // au lieu de forcer un lacet à zéro (ce qui figeait la caméra "droit devant").
    if (horizontal > 0.6) {
      targetYaw = Math.atan2(dir.x, dir.z);
    }
  } else if (!rocketState.launched) {
    // Sur la rampe, le nez est parfaitement vertical (composante horizontale
    // nulle) : on suit directement le cap visé plutôt que la direction du nez.
    targetYaw = rocketState.heading;
  } else {
    const nose = FORWARD_LOCAL.clone().applyQuaternion(rocketState.orientation);
    targetYaw = Math.atan2(nose.x, nose.z);
  }

  let yawDiff = targetYaw - cameraRig.yaw;
  yawDiff = Math.atan2(Math.sin(yawDiff), Math.cos(yawDiff));
  const turnSmooth = 1 - Math.pow(0.001, dt * CAMERA_TURN_SMOOTH * 0.3);
  cameraRig.yaw += yawDiff * turnSmooth;

  const back = new THREE.Vector3(-Math.sin(cameraRig.yaw), 0, -Math.cos(cameraRig.yaw));
  const desired = rocketState.position.clone()
    .addScaledVector(back, CAMERA_DISTANCE_BACK)
    .add(new THREE.Vector3(0, CAMERA_HEIGHT_ABOVE, 0));

  const lerpFactor = 1 - Math.pow(0.001, dt);
  cameraRig.position.lerp(desired, lerpFactor);
  cameraRig.lookTarget.lerp(rocketState.position, lerpFactor);

  cameraShake.intensity *= Math.max(0, 1 - 6 * dt);
  const shakeOffset = new THREE.Vector3(
    (Math.random() - 0.5) * cameraShake.intensity,
    (Math.random() - 0.5) * cameraShake.intensity,
    (Math.random() - 0.5) * cameraShake.intensity
  );

  camera.position.copy(cameraRig.position).add(shakeOffset);

  // Balayage libre de l'environnement au clic-glissé : incline la direction
  // du regard autour de la cible habituelle, sans jamais affecter la
  // trajectoire ni l'orientation réelle du missile. Dès qu'on relâche, la
  // vue se recentre doucement sur la cible normale.
  const lookTargetX = dragLooking ? mouseLook.x : 0;
  const lookTargetY = dragLooking ? mouseLook.y : 0;
  smoothedMouseLook.x = THREE.MathUtils.lerp(smoothedMouseLook.x, lookTargetX, 1 - Math.pow(0.0005, dt));
  smoothedMouseLook.y = THREE.MathUtils.lerp(smoothedMouseLook.y, lookTargetY, 1 - Math.pow(0.0005, dt));

  // Paramétrage sphérique direct (lacet/tangage purs) au lieu de rotations en
  // chaîne : évite tout désaxage de l'axe de tangage quand on glisse en
  // diagonale (c'était la cause de la rotation erratique précédente).
  const baseViewPitch = -Math.atan2(CAMERA_HEIGHT_ABOVE, CAMERA_DISTANCE_BACK);
  const viewYaw = cameraRig.yaw + smoothedMouseLook.x * MOUSE_LOOK_YAW;
  const viewPitch = THREE.MathUtils.clamp(
    baseViewPitch + smoothedMouseLook.y * MOUSE_LOOK_PITCH, -1.5, 1.5
  );
  const lookDir = new THREE.Vector3(
    Math.sin(viewYaw) * Math.cos(viewPitch),
    Math.sin(viewPitch),
    Math.cos(viewYaw) * Math.cos(viewPitch)
  );

  camera.lookAt(camera.position.clone().add(lookDir.multiplyScalar(100)));

  water.position.x = rocketState.position.x;
  water.position.z = rocketState.position.z;

  updateTargetIndicators();
}

/* ------------------------------------------------------------------ */
/*  HUD                                                                 */
/* ------------------------------------------------------------------ */

const speedValue = document.getElementById("speedValue");
const altValue = document.getElementById("altValue");
const throttleLamp = document.getElementById("throttleLamp");
const attitudeCanvas = document.getElementById("attitudeCanvas");
const attitudeCtx = attitudeCanvas.getContext("2d");

function updateHud(speed, alt) {
  throttleLamp.classList.toggle("on", rocketState.thrustOn);
  speedValue.textContent = Math.round(speed);
  altValue.textContent = Math.round(Math.max(0, alt));
  drawAttitudeIndicator();
}

// Horizon artificiel façon gyroscope d'avion : incline et translate le plan
// ciel/sol selon le roulis (cosmétique) et le tangage réel du missile.
function drawAttitudeIndicator() {
  const ctx = attitudeCtx;
  const w = attitudeCanvas.width, h = attitudeCanvas.height;
  const cx = w / 2, cy = h / 2, r = w / 2;

  const forward = FORWARD_LOCAL.clone().applyQuaternion(rocketState.orientation);
  const pitch = Math.asin(THREE.MathUtils.clamp(forward.y, -1, 1));
  const roll = rocketState.roll;

  ctx.clearRect(0, 0, w, h);
  ctx.save();
  ctx.beginPath();
  ctx.arc(cx, cy, r - 2, 0, Math.PI * 2);
  ctx.clip();

  ctx.translate(cx, cy);
  ctx.rotate(-roll);
  ctx.translate(0, pitch * (h * 0.7));

  ctx.fillStyle = "#3f7fd9";
  ctx.fillRect(-w * 1.5, -h * 3, w * 3, h * 3);
  ctx.fillStyle = "#7a5230";
  ctx.fillRect(-w * 1.5, 0, w * 3, h * 3);
  ctx.strokeStyle = "#eafff2";
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(-w * 1.5, 0);
  ctx.lineTo(w * 1.5, 0);
  ctx.stroke();

  ctx.restore();

  ctx.strokeStyle = "#ffcf4d";
  ctx.lineWidth = 3;
  ctx.beginPath();
  ctx.moveTo(cx - 22, cy);
  ctx.lineTo(cx - 7, cy);
  ctx.moveTo(cx + 7, cy);
  ctx.lineTo(cx + 22, cy);
  ctx.stroke();
  ctx.beginPath();
  ctx.arc(cx, cy, 2.5, 0, Math.PI * 2);
  ctx.fillStyle = "#ffcf4d";
  ctx.fill();

  ctx.strokeStyle = "rgba(234, 255, 242, 0.35)";
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.arc(cx, cy, r - 2, 0, Math.PI * 2);
  ctx.stroke();
}

/* ------------------------------------------------------------------ */
/*  Radar + flèche de cap vers la cible (mode Cible)                    */
/* ------------------------------------------------------------------ */

const RADAR_RANGE = 1400;
const RADAR_RADIUS_PX = 65;

const radarEl = document.getElementById("radar");
const radarPlaneEl = document.getElementById("radarPlane");
const targetArrowEl = document.getElementById("targetArrow");
const targetBoxEl = document.getElementById("targetBox");

function updateTargetIndicators() {
  const info = getTargetInfo();
  const show = !!info;
  radarEl.classList.toggle("hidden", !show);
  targetArrowEl.classList.toggle("hidden", !show);
  if (!show) {
    targetBoxEl.classList.add("hidden");
    return;
  }

  // Radar : plan vu de dessus, non tourné (nord fixe), centré sur le missile.
  const dx = info.position.x - rocketState.position.x;
  const dz = info.position.z - rocketState.position.z;
  const rx = THREE.MathUtils.clamp((dx / RADAR_RANGE) * RADAR_RADIUS_PX, -RADAR_RADIUS_PX, RADAR_RADIUS_PX);
  const rz = THREE.MathUtils.clamp((dz / RADAR_RANGE) * RADAR_RADIUS_PX, -RADAR_RADIUS_PX, RADAR_RADIUS_PX);
  radarPlaneEl.style.transform = `translate(${rx - 4}px, ${rz - 4}px)`;

  // Flèche : simple différence de cap horizontal (lacet) entre la caméra et
  // la cible, en 2D pur — pas de produits scalaires 3D ni de dépendance à
  // l'orientation de la caméra, donc pas de cas dégénéré ni de à-coups.
  const viewYaw = cameraRig.yaw + smoothedMouseLook.x * MOUSE_LOOK_YAW;
  const bearing = Math.atan2(dx, dz);
  let angle = bearing - viewYaw;
  angle = Math.atan2(Math.sin(angle), Math.cos(angle));
  targetArrowEl.style.transform = `translate(-50%, -50%) translateY(-46px) rotate(${angle}rad)`;

  // Carré de verrouillage : affiché uniquement quand la cible est réellement
  // dans le champ de la caméra (devant, et dans les limites de l'écran).
  const camDir = new THREE.Vector3();
  camera.getWorldDirection(camDir);
  const inFront = info.position.clone().sub(camera.position).dot(camDir) > 0;

  if (inFront) {
    const ndc = info.position.clone().project(camera);
    if (ndc.x >= -1 && ndc.x <= 1 && ndc.y >= -1 && ndc.y <= 1) {
      const screenX = (ndc.x * 0.5 + 0.5) * window.innerWidth;
      const screenY = (-ndc.y * 0.5 + 0.5) * window.innerHeight;
      targetBoxEl.style.left = screenX + "px";
      targetBoxEl.style.top = screenY + "px";
      targetBoxEl.classList.remove("hidden");
    } else {
      targetBoxEl.classList.add("hidden");
    }
  } else {
    targetBoxEl.classList.add("hidden");
  }
}

/* ------------------------------------------------------------------ */
/*  Boucle principale                                                   */
/* ------------------------------------------------------------------ */

function animate() {
  requestAnimationFrame(animate);
  const dt = Math.min(clock.getDelta(), 0.05);
  const elapsed = clock.getElapsedTime();

  // Tant qu'aucun mode n'a été choisi dans le menu, aucune partie n'existe
  // encore (pas de missile construit) : on se contente de rendre la scène vide.
  if (!menuOpen && rocket) {
    updateRocket(dt, elapsed);
    updateSmoke(dt);
    updateFlashLights(dt);
    updatePlane(dt, elapsed);
    checkTargetHit();
    updateCamera(dt);

    sinceChunkUpdate += dt;
    if (sinceChunkUpdate > 0.3) {
      updateChunks(rocketState.position.x, rocketState.position.z);
      updateSkyCells(rocketState.position.x, rocketState.position.z);
      sinceChunkUpdate = 0;
    }
  }

  renderer.render(scene, camera);
}

init();
