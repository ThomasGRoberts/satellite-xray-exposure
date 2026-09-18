import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import * as topojson from "./vendor/topojson-client.js";
import * as satellite from "./vendor/satellite.es.js";
import { calculatePromptExposure, PERMANENT_DAMAGE_THRESHOLD_J_M2, thresholdRadiusMeters, segmentIntersectsSphere } from "./prompt-effects.js";

const EARTH_RADIUS_KM = 6378.137;
const SCALE = 1 / EARTH_RADIUS_KM;
const SATELLITE_SPRITE_SCALE = 0.018;
const CATALOG_METADATA_URL = "data/catalog/catalog-metadata.json";
const ANALYSIS_METADATA_URL = "data/catalog/analysis-metadata.json";
const BASE_PLAYBACK_SIM_HOURS_PER_REAL_SECOND = 0.02;
const MU_EARTH_KM3_S2 = 398600.4418;
const EARTH_ROTATION_RATE_RAD_PER_SEC = 7.292115e-5;
const PROPAGATION_KEYFRAME_SECONDS = 120;
const MIN_CARRIER_PERIGEE_KM = 100;
const COUNTDOWN_DURATION_MS = 3000;
const POST_CAMERA_HOLD_MS = 450;
const BLAST_ANIMATION_DURATION_MS = 9800;
const AFTERGLOW_HOLD_MS = 7000;
const AFTERGLOW_FADE_MS = 9000;
const DETONATION_WASH_RISE_MS = 650;
const DETONATION_WASH_HOLD_MS = 2200;
const DETONATION_WASH_FADE_MS = 9000;
const DETONATION_WASH_MAX_OPACITY = 0.16;
const RESULTS_PLAYBACK_SIM_SECONDS_PER_REAL_SECOND = 72;
// Fixed display-only count-distribution settings in log10(J/m²); never used by physics, colors, filters, or threshold counts.
const COUNT_DISTRIBUTION_INTERVALS = 64;
const COUNT_SMOOTHING_SIGMA_INTERVALS = 1.35;
const DETONATION_CAMERA_RANGE_EARTH_RADII = 2.35;
// Relative screen composition measured from preferred regression calibration 004.
const DETONATION_APPARENT_RADIUS_FRACTION = 0.6545;
const DETONATION_EFFECT_FRAME_FRACTION = 0.78;
const EARTH_NORTH = new THREE.Vector3(0, 1, 0);
const INTERFACE_DARK_TEXT = "#444444";
const STATISTIC_CARD_BACKGROUND = "#ffffff";
const LARGE_TEXT_MINIMUM_CONTRAST = 3;
const CARRIER_OUTLINE = Object.freeze({ color: "#4d4d4d", opacity: 1 });
window.__carrierOutlineAudit = { token: CARRIER_OUTLINE, trajectory: null, marker: null };

const scene = new THREE.Scene();
const SKY_BASE_COLOR = new THREE.Color(0xffffff), SKY_AFTERGLOW_COLOR = new THREE.Color(0xfffdf6);
scene.background = SKY_BASE_COLOR.clone();
document.body.dataset.sky = "base";
const camera = new THREE.PerspectiveCamera(38, innerWidth / innerHeight, 0.01, 1000);
const renderer = new THREE.WebGLRenderer({ antialias: true, preserveDrawingBuffer: true });
renderer.setSize(innerWidth, innerHeight);
renderer.setPixelRatio(devicePixelRatio);
renderer.sortObjects = true;
document.getElementById("canvas-wrap").appendChild(renderer.domElement);
const payloadRaycaster = new THREE.Raycaster(), payloadPointer = new THREE.Vector2();
payloadRaycaster.params.Points.threshold = .02;

const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.enablePan = true;
controls.screenSpacePanning = true;
const earthGroup = new THREE.Group();
const countryLineGroup = new THREE.Group();
const trajectoryGroup = new THREE.Group();
const constellationGroup = new THREE.Group();
scene.add(earthGroup, countryLineGroup, trajectoryGroup, constellationGroup);

let catalog = [], catalogSatrecs = [], catalogSearch = [], visualOrbits = [], points = null, carrierSprite = null, carrierTrajectory = null, catalogMetadata = null, ownerCodeMetadata = null, analysisMetadata = null;
let renderIndexByCatalogId = new Map();
const APP_STATES = Object.freeze({ LOADING: "loading", RUNNING: "running", PAUSED: "paused", COUNTDOWN: "detonation-countdown", DETONATION: "detonation-animation", RESULTS: "results-displayed" });
let appState = APP_STATES.LOADING, simulationSeconds = 0, isPlaying = false, playbackMultiplier = 1;
let catalogEpoch = new Date(), lastFrameTime = performance.now();
let populationFrameStart = NaN, populationFrame0 = null, populationFrame1 = null, propagatedCount = 0;
let populationRevealStartedAt = null;
let blastShell = null, blastStartedAt = null, blastFinalScale = 0, blastWaveMaxScale = 0;
let afterglowStartedAt = null;
let blastResults = null;
let detonationSequence = null, detonationFlash = null;
let promptWorker = null, promptWorkerReady = null, promptWorkerRequestId = 0;
const promptWorkerRequests = new Map();
const CATEGORY_STATES = Object.freeze({ NEUTRAL: "neutral", FOCUS: "focus", EXCLUDE: "exclude" });
let selectedAnalysisThreshold = 40, selectedCountryDrilldowns = new Map(), selectedMissionDrilldowns = new Map(), selectedConstellationDrilldowns = new Map();
let resultsPlaybackPlaying = false, resultsPlaybackMultiplier = 1, resultDetonationSimulationSeconds = 0, resultPlaybackSeconds = 0, resultFrameStart = NaN, resultFrame0 = null, resultFrame1 = null, resultPlaybackCatalogIds = [];
let resultVisualStates = [], resultPlaybackContinuityFrame = null;
let resultsHomeReturnStarted = false;
let yieldPreview = null, yieldPreviewPuffStartedAt = null, cameraTransition = null;
let carrierDrawStartedAt = null, carrierPulseStartedAt = null, nextCarrierPulseAt = Infinity;
let carrierShimmerStartedAt = null, carrierShimmer = null, orbitPresentationTimer = null, orbitPresentationResumePending = false;
let carrierTrajectoryUpdateFrame = null, carrierTrajectorySamples = [];
let carrierTrackingInteracting = false, carrierTrackingSuppressedUntil = 0;
let pendingCarrierPresentation = null;
let thresholdNudgeShown = false, thresholdNudgeAnimation = null, thresholdSlideAnimation = null;
let timingAnalysisRunId = 0, timingAnalysisResult = null;
let satelliteHoverFrame = null, latestSatelliteHoverEvent = null;
const CARRIER_TRACKING_RESUME_DELAY_MS = 3200;
const carrierOrbit = { semiMajor: EARTH_RADIUS_KM + 2000, eccentricity: 0, inclination: THREE.MathUtils.degToRad(67.1), raan: THREE.MathUtils.degToRad(35), argPerigee: 0, epochAnomaly: 0 };
let carrierBaseOrbit = { ...carrierOrbit };
let carrierBaseLabel = "Candidate orbit";
let carrierBaseCatalogId = null;
const sharedScenario = parseSharedScenario(location.search);

function parseSharedScenario(search) {
  const params = new URLSearchParams(search);
  if (params.get("scenario") !== "v1") return null;
  const numeric = key => Number(params.get(key));
  const orbit = { semiMajor: numeric("a"), eccentricity: numeric("e"), inclination: numeric("i"), raan: numeric("raan"), argPerigee: numeric("argp"), epochAnomaly: numeric("m0") };
  const epoch = new Date(params.get("epoch") || "");
  const yieldKt = numeric("yield"), threshold = numeric("threshold");
  if (!params.get("snapshot") || !Number.isFinite(epoch.getTime()) || !(threshold > 0) || ![yieldKt, threshold, ...Object.values(orbit)].every(Number.isFinite)) return { error: "The shared scenario URL is incomplete or invalid." };
  return { snapshot: params.get("snapshot"), epoch, yieldKt, threshold, orbit, carrierId: params.get("carrier") || null };
}

function makeSatelliteSpriteTexture(fillColor, strokeColor, strokeWidth = 18, strokeOpacity = 1) {
  const canvas = document.createElement("canvas"); canvas.width = canvas.height = 128;
  const context = canvas.getContext("2d"); context.beginPath(); context.arc(64, 64, 37, 0, Math.PI * 2);
  context.fillStyle = fillColor; context.fill(); context.lineWidth = strokeWidth; context.strokeStyle = strokeColor; context.globalAlpha = strokeOpacity; context.stroke(); context.globalAlpha = 1;
  const texture = new THREE.CanvasTexture(canvas); texture.needsUpdate = true; return texture;
}

function makePayloadPointMaterial() {
  const canvas = document.createElement("canvas"); canvas.width = canvas.height = 64; const context = canvas.getContext("2d"); context.beginPath(); context.arc(32, 32, 24, 0, Math.PI * 2); context.fillStyle = "#fff"; context.fill(); const texture = new THREE.CanvasTexture(canvas);
  return new THREE.ShaderMaterial({ uniforms: { pointTexture: { value: texture }, pixelRatio: { value: Math.min(devicePixelRatio, 2) }, focusScale: { value: 1 }, revealOpacity: { value: 0 } }, vertexShader: `uniform float pixelRatio; uniform float focusScale; attribute vec3 effectColor; attribute float effectAlpha; attribute float effectScale; varying vec3 vColor; varying float vAlpha; void main(){ vec4 mvPosition=modelViewMatrix*vec4(position,1.0); float depthFactor=clamp(4.0/max(0.01,-mvPosition.z),0.88,1.22); gl_PointSize=2.75*pixelRatio*depthFactor*focusScale*effectScale; gl_Position=projectionMatrix*mvPosition; vColor=effectColor; vAlpha=effectAlpha; }`, fragmentShader: `uniform sampler2D pointTexture; uniform float revealOpacity; varying vec3 vColor; varying float vAlpha; void main(){ vec4 sampleColor=texture2D(pointTexture,gl_PointCoord); if(sampleColor.a<0.02) discard; gl_FragColor=vec4(vColor,vAlpha*sampleColor.a*revealOpacity); }`, transparent: true, depthTest: true, depthWrite: false });
}

function makeFallbackEarth() {
  const earth = new THREE.Mesh(new THREE.SphereGeometry(1, 160, 160), new THREE.MeshBasicMaterial({ color: 0xf7f7f7, depthTest: true, depthWrite: true }));
  earth.renderOrder = 0; earthGroup.add(earth);
}

function latLonToVector3(latDeg, lonDeg, radius = 1) {
  const lat = THREE.MathUtils.degToRad(latDeg), lon = THREE.MathUtils.degToRad(lonDeg);
  return new THREE.Vector3(radius * Math.cos(lat) * Math.cos(lon), radius * Math.sin(lat), -radius * Math.cos(lat) * Math.sin(lon));
}

async function loadWorldBoundaries() {
  const response = await fetch("data/geo/countries-110m.json");
  if (!response.ok) throw new Error(`World boundaries request failed: ${response.status}`);
  const topology = await response.json();
  topojson.feature(topology, topology.objects.countries).features.forEach(feature => addCountryBoundary(feature.geometry));
}

function addCountryBoundary(geometry) {
  if (!geometry) return;
  if (geometry.type === "Polygon") geometry.coordinates.forEach(addBoundaryTube);
  if (geometry.type === "MultiPolygon") geometry.coordinates.forEach(poly => poly.forEach(addBoundaryTube));
}

function addBoundaryTube(ring) {
  if (!ring || ring.length < 3) return;
  const points = ring.map(([lon, lat]) => latLonToVector3(lat, lon, 1.001));
  const curve = new THREE.CatmullRomCurve3(points, true);
  const geometry = new THREE.TubeGeometry(curve, Math.max(24, points.length * 2), 0.00068, 5, true);
  const material = new THREE.MeshBasicMaterial({ color: 0x777777, transparent: true, opacity: 0.88, depthTest: true, depthWrite: false });
  const tube = new THREE.Mesh(geometry, material); tube.renderOrder = 3; countryLineGroup.add(tube);
}

function solveEccentricAnomaly(meanAnomaly, eccentricity) {
  let eccentricAnomaly = meanAnomaly;
  for (let i = 0; i < 5; i++) eccentricAnomaly -= (eccentricAnomaly - eccentricity * Math.sin(eccentricAnomaly) - meanAnomaly) / (1 - eccentricity * Math.cos(eccentricAnomaly));
  return eccentricAnomaly;
}

function greenwichSiderealAngle(date) {
  const julianDate = date.getTime() / 86400000 + 2440587.5;
  const centuries = (julianDate - 2451545) / 36525;
  return THREE.MathUtils.degToRad((280.46061837 + 360.98564736629 * (julianDate - 2451545) + 0.000387933 * centuries * centuries) % 360);
}

function visualPositionAt(index, date) {
  const orbit = visualOrbits[index], elapsed = (date.getTime() - orbit.epochMs) / 1000;
  const meanAnomaly = orbit.meanAnomaly + orbit.meanMotion * elapsed;
  const eccentricAnomaly = solveEccentricAnomaly(meanAnomaly, orbit.eccentricity);
  const xOrbital = orbit.semiMajor * (Math.cos(eccentricAnomaly) - orbit.eccentricity);
  const yOrbital = orbit.semiMajor * Math.sqrt(1 - orbit.eccentricity * orbit.eccentricity) * Math.sin(eccentricAnomaly);
  const cosO = Math.cos(orbit.raan), sinO = Math.sin(orbit.raan), cosI = Math.cos(orbit.inclination), sinI = Math.sin(orbit.inclination), cosW = Math.cos(orbit.argPerigee), sinW = Math.sin(orbit.argPerigee);
  const xPerifocal = xOrbital * cosW - yOrbital * sinW, yPerifocal = xOrbital * sinW + yOrbital * cosW;
  const fixed = new THREE.Vector3(xPerifocal * cosO - yPerifocal * sinO * cosI, yPerifocal * sinI, -(xPerifocal * sinO + yPerifocal * cosO * cosI));
  fixed.applyAxisAngle(new THREE.Vector3(0, 1, 0), -greenwichSiderealAngle(date));
  return fixed.multiplyScalar(SCALE);
}

function computePopulationFrame(seconds) {
  const date = new Date(catalogEpoch.getTime() + seconds * 1000);
  const frame = new Float32Array(catalog.length * 3);
  let valid = 0;
  for (let i = 0; i < visualOrbits.length; i++) {
    const p = visualPositionAt(i, date), j = i * 3;
    if (p) { frame[j] = p.x; frame[j + 1] = p.y; frame[j + 2] = p.z; valid++; }
  }
  propagatedCount = valid;
  return frame;
}

function stateVectorToTwoBodyVisualState(positionArray, velocityArray, index) {
  const offset = index * 3, position = new THREE.Vector3(positionArray[offset], positionArray[offset + 1], positionArray[offset + 2]), velocity = new THREE.Vector3(velocityArray[offset], velocityArray[offset + 1], velocityArray[offset + 2]);
  if (![...position, ...velocity].every(Number.isFinite)) return null;
  const radius = position.length(), speedSquared = velocity.lengthSq(), angularMomentum = new THREE.Vector3().crossVectors(position, velocity), angularMomentumUnit = angularMomentum.clone().normalize();
  const eccentricityVector = new THREE.Vector3().crossVectors(velocity, angularMomentum).multiplyScalar(1 / MU_EARTH_KM3_S2).sub(position.clone().multiplyScalar(1 / radius));
  const eccentricity = eccentricityVector.length(), semiMajor = 1 / (2 / radius - speedSquared / MU_EARTH_KM3_S2);
  if (!(semiMajor > 0) || !(eccentricity >= 0) || eccentricity >= 1 || angularMomentum.lengthSq() < 1e-12) return null;
  const periapsisDirection = eccentricity > 1e-8 ? eccentricityVector.clone().normalize() : position.clone().normalize(), quadratureDirection = new THREE.Vector3().crossVectors(angularMomentumUnit, periapsisDirection).normalize();
  const cosE = THREE.MathUtils.clamp(position.dot(periapsisDirection) / semiMajor + eccentricity, -1, 1), sinE = position.dot(quadratureDirection) / (semiMajor * Math.sqrt(1 - eccentricity * eccentricity)), eccentricAnomaly = Math.atan2(sinE, cosE);
  return { semiMajor, eccentricity, periapsisDirection, quadratureDirection, meanAnomalyAtDetonation: eccentricAnomaly - eccentricity * Math.sin(eccentricAnomaly), meanMotion: Math.sqrt(MU_EARTH_KM3_S2 / Math.pow(semiMajor, 3)) };
}

function initializeResultVisualStates(positionsEciKm, velocitiesEciKmS) {
  resultVisualStates = catalog.map((_, index) => stateVectorToTwoBodyVisualState(positionsEciKm, velocitiesEciKmS, index));
}

function computeResultPopulationFrame(elapsedSeconds) {
  const date = new Date(catalogEpoch.getTime() + (resultDetonationSimulationSeconds + elapsedSeconds) * 1000), gmst = satellite.gstime(date), frame = new Float32Array(catalog.length * 3); frame.fill(NaN);
  resultVisualStates.forEach((state, index) => {
    if (!state) return;
    const meanAnomaly = state.meanAnomalyAtDetonation + state.meanMotion * elapsedSeconds, eccentricAnomaly = solveEccentricAnomaly(meanAnomaly, state.eccentricity), positionEci = state.periapsisDirection.clone().multiplyScalar(state.semiMajor * (Math.cos(eccentricAnomaly) - state.eccentricity)).addScaledVector(state.quadratureDirection, state.semiMajor * Math.sqrt(1 - state.eccentricity * state.eccentricity) * Math.sin(eccentricAnomaly)), scenePosition = ecfKmToScene(satellite.eciToEcf(positionEci, gmst)), offset = index * 3;
    frame[offset] = scenePosition.x; frame[offset + 1] = scenePosition.y; frame[offset + 2] = scenePosition.z;
  });
  return frame;
}

function updateSatellitePositions(force = false) {
  const bracket = Math.floor(simulationSeconds / PROPAGATION_KEYFRAME_SECONDS) * PROPAGATION_KEYFRAME_SECONDS;
  if (force || bracket !== populationFrameStart) {
    const canReuseNext = !force && bracket === populationFrameStart + PROPAGATION_KEYFRAME_SECONDS && populationFrame1;
    const previousNext = populationFrame1;
    populationFrameStart = bracket;
    populationFrame0 = canReuseNext ? previousNext : computePopulationFrame(bracket);
    populationFrame1 = computePopulationFrame(bracket + PROPAGATION_KEYFRAME_SECONDS);
  }
  const alpha = (simulationSeconds - populationFrameStart) / PROPAGATION_KEYFRAME_SECONDS;
  const positions = points.geometry.attributes.position.array;
  for (let i = 0; i < positions.length; i++) positions[i] = populationFrame0[i] + (populationFrame1[i] - populationFrame0[i]) * alpha;
  points.geometry.attributes.position.needsUpdate = true;
  if (carrierSprite) carrierSprite.position.copy(carrierPosition(simulationSeconds));
  if (yieldPreview && carrierSprite) yieldPreview.position.copy(carrierSprite.position);
  trajectoryGroup.rotation.y = -EARTH_ROTATION_RATE_RAD_PER_SEC * simulationSeconds;
}

function carrierElements() {
  return carrierOrbit;
}

function carrierPerigeeKm(orbit = carrierOrbit) { return orbit.semiMajor * (1 - orbit.eccentricity) - EARTH_RADIUS_KM; }
function carrierOrbitIsValid(orbit) { return Number.isFinite(carrierPerigeeKm(orbit)) && carrierPerigeeKm(orbit) >= MIN_CARRIER_PERIGEE_KM - 1e-6; }
function showOrbitConstraint(show = true) { document.getElementById("orbitConstraintMessage").hidden = !show; }

function orbitPlanePoint(e, trueAnomaly, rotateEarth = true, earthRotationSeconds = simulationSeconds) {
  const radius = e.semiMajor * (1 - e.eccentricity * e.eccentricity) / (1 + e.eccentricity * Math.cos(trueAnomaly)) * SCALE, argumentLatitude = e.argPerigee + trueAnomaly;
  const xOrb = radius * Math.cos(argumentLatitude), yOrb = radius * Math.sin(argumentLatitude);
  const vector = new THREE.Vector3(xOrb * Math.cos(e.raan) - yOrb * Math.sin(e.raan) * Math.cos(e.inclination), yOrb * Math.sin(e.inclination), -(xOrb * Math.sin(e.raan) + yOrb * Math.cos(e.raan) * Math.cos(e.inclination)));
  if (rotateEarth) vector.applyAxisAngle(new THREE.Vector3(0, 1, 0), -EARTH_ROTATION_RATE_RAD_PER_SEC * earthRotationSeconds);
  return vector;
}
function carrierPlanePoint(trueAnomaly, rotateEarth = true, earthRotationSeconds = simulationSeconds) { return orbitPlanePoint(carrierElements(), trueAnomaly, rotateEarth, earthRotationSeconds); }

function carrierPosition(seconds) {
  const e = carrierElements(), eccentricAnomaly0 = 2 * Math.atan2(Math.sqrt(1 - e.eccentricity) * Math.sin(e.epochAnomaly / 2), Math.sqrt(1 + e.eccentricity) * Math.cos(e.epochAnomaly / 2));
  const meanAnomaly = eccentricAnomaly0 - e.eccentricity * Math.sin(eccentricAnomaly0) + Math.sqrt(MU_EARTH_KM3_S2 / Math.pow(e.semiMajor, 3)) * seconds;
  const eccentricAnomaly = solveEccentricAnomaly(meanAnomaly, e.eccentricity);
  const trueAnomaly = 2 * Math.atan2(Math.sqrt(1 + e.eccentricity) * Math.sin(eccentricAnomaly / 2), Math.sqrt(1 - e.eccentricity) * Math.cos(eccentricAnomaly / 2));
  return carrierPlanePoint(trueAnomaly, true, seconds);
}

function makeCarrierTrajectory(animateEntrance = true) {
  const samples = [];
  for (let i = 0; i < 240; i++) samples.push(carrierPlanePoint(i / 240 * Math.PI * 2, false));
  carrierTrajectorySamples = samples.map(point => point.clone());
  if (carrierTrajectory) { trajectoryGroup.remove(carrierTrajectory); carrierTrajectory.traverse(child => { if (child.geometry) child.geometry.dispose(); if (child.material) child.material.dispose(); }); }
  carrierTrajectory = new THREE.Group();
  const curve = new THREE.CatmullRomCurve3(samples, true), base = new THREE.Mesh(new THREE.TubeGeometry(curve, 240, .0016, 5, true), new THREE.MeshBasicMaterial({ color: CARRIER_OUTLINE.color, transparent: true, opacity: CARRIER_OUTLINE.opacity, depthTest: true, depthWrite: false }));
  base.userData.carrierOutline = CARRIER_OUTLINE;
  const accent = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(samples), new THREE.LineDashedMaterial({ color: 0xeaaa00, transparent: true, opacity: .9, dashSize: .035, gapSize: .055, depthTest: true, depthWrite: false })); accent.computeLineDistances();
  carrierShimmer = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(samples), new THREE.LineBasicMaterial({ color: 0xffdf66, transparent: true, opacity: 0, depthTest: true, depthWrite: false }));
  [base, accent, carrierShimmer].forEach(object => { object.userData.fullDrawCount = object.geometry.index ? object.geometry.index.count : object.geometry.attributes.position.count; object.geometry.setDrawRange(0, animateEntrance ? 0 : object.userData.fullDrawCount); });
  base.renderOrder = 6; accent.renderOrder = 7; carrierShimmer.renderOrder = 8; carrierTrajectory.add(base, accent, carrierShimmer); trajectoryGroup.add(carrierTrajectory);
  window.__carrierOutlineAudit.trajectory = { color: `#${base.material.color.getHexString()}`, opacity: base.material.opacity };
  carrierDrawStartedAt = animateEntrance ? performance.now() : null; carrierShimmerStartedAt = animateEntrance ? performance.now() : null; carrierShimmer.material.opacity = 0;
  trajectoryGroup.rotation.y = -EARTH_ROTATION_RATE_RAD_PER_SEC * simulationSeconds;
  if (carrierSprite) carrierSprite.position.copy(carrierPosition(simulationSeconds));
}

function ensureCarrierOrbitInFrame() {
  if (!carrierTrajectorySamples.length) return;
  camera.updateMatrixWorld(); camera.updateProjectionMatrix();
  let extent = 0;
  for (let i = 0; i < carrierTrajectorySamples.length; i += 8) { const projected = carrierTrajectorySamples[i].clone().applyAxisAngle(new THREE.Vector3(0, 1, 0), trajectoryGroup.rotation.y).project(camera); extent = Math.max(extent, Math.abs(projected.x), Math.abs(projected.y)); }
  if (extent > .92) { const factor = Math.min(1.035, extent / .90), direction = camera.position.clone().sub(controls.target).multiplyScalar(factor); camera.position.copy(controls.target).add(direction); controls.update(); }
}
function scheduleInteractiveTrajectoryUpdate() { if (carrierTrajectoryUpdateFrame !== null) return; carrierTrajectoryUpdateFrame = requestAnimationFrame(() => { carrierTrajectoryUpdateFrame = null; makeCarrierTrajectory(false); ensureCarrierOrbitInFrame(); }); }

function renderCarrier() {
  if (carrierSprite) return;
  const material = new THREE.SpriteMaterial({ map: makeSatelliteSpriteTexture("#eaaa00", CARRIER_OUTLINE.color, 18, CARRIER_OUTLINE.opacity), transparent: true, depthTest: true, depthWrite: false, alphaTest: .02 });
  material.userData.carrierOutline = CARRIER_OUTLINE;
  const carrierScale = SATELLITE_SPRITE_SCALE * 1.9;
  carrierSprite = new THREE.Sprite(material); carrierSprite.scale.set(carrierScale, carrierScale, 1); carrierSprite.userData.baseScale = carrierScale; carrierSprite.renderOrder = 9; constellationGroup.add(carrierSprite);
  window.__carrierOutlineAudit.marker = { color: CARRIER_OUTLINE.color, opacity: CARRIER_OUTLINE.opacity };
  window.__carrierOutlineAudit.identical = window.__carrierOutlineAudit.trajectory?.color === window.__carrierOutlineAudit.marker.color && window.__carrierOutlineAudit.trajectory?.opacity === window.__carrierOutlineAudit.marker.opacity;
  if (!carrierTrajectory) makeCarrierTrajectory(); carrierSprite.position.copy(carrierPosition(simulationSeconds));
  nextCarrierPulseAt = performance.now() + 2600;
}

function renderCatalog() {
  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute("position", new THREE.BufferAttribute(new Float32Array(catalog.length * 3), 3));
  const colors = new Float32Array(catalog.length * 3), scales = new Float32Array(catalog.length), alphas = new Float32Array(catalog.length);
  for (let i = 0; i < catalog.length; i++) { colors[i * 3] = colors[i * 3 + 1] = colors[i * 3 + 2] = 0.56; scales[i] = 1; alphas[i] = 0.48; }
  geometry.setAttribute("effectColor", new THREE.BufferAttribute(colors, 3)); geometry.setAttribute("effectScale", new THREE.BufferAttribute(scales, 1)); geometry.setAttribute("effectAlpha", new THREE.BufferAttribute(alphas, 1));
  const material = makePayloadPointMaterial();
  points = new THREE.Points(geometry, material); points.renderOrder = 8; constellationGroup.add(points);
  populationRevealStartedAt = performance.now();
  updateSatellitePositions(true);
}

function initializePromptWorker() {
  promptWorker = new Worker(new URL("./prompt-worker.js", import.meta.url), { type: "module" });
  promptWorkerReady = new Promise((resolve, reject) => {
    promptWorker.onmessage = event => {
      if (event.data.type === "ready") { resolve(); return; }
      if (event.data.type === "result") { const pending = promptWorkerRequests.get(event.data.requestId); if (pending) { promptWorkerRequests.delete(event.data.requestId); pending.resolve(event.data); } }
    };
    promptWorker.onerror = error => reject(new Error(`Prompt-effects worker failed: ${error.message}`));
  });
  promptWorker.postMessage({ type: "initialize", catalog });
  return promptWorkerReady;
}

async function requestPromptCalculation(payload) {
  await promptWorkerReady; const requestId = ++promptWorkerRequestId;
  return new Promise((resolve, reject) => { promptWorkerRequests.set(requestId, { resolve, reject }); promptWorker.postMessage({ type: "calculate", requestId, ...payload }); });
}

async function loadCatalog() {
  const [metadataResponse, ownerCodeResponse, analysisMetadataResponse] = await Promise.all([fetch(CATALOG_METADATA_URL, { cache: "no-store" }), fetch("data/owner-code-labels.json", { cache: "no-store" }), fetch(ANALYSIS_METADATA_URL, { cache: "no-store" })]);
  if (!metadataResponse.ok) throw new Error(`Catalog metadata request failed: ${metadataResponse.status}`);
  if (!ownerCodeResponse.ok) throw new Error(`Owner-code mapping request failed: ${ownerCodeResponse.status}`);
  if (!analysisMetadataResponse.ok) throw new Error(`Analysis metadata request failed: ${analysisMetadataResponse.status}`);
  const metadata = await metadataResponse.json();
  ownerCodeMetadata = await ownerCodeResponse.json();
  analysisMetadata = await analysisMetadataResponse.json();
  catalogMetadata = metadata;
  if (sharedScenario && sharedScenario.error) throw new Error(sharedScenario.error);
  const requestedSnapshot = sharedScenario ? sharedScenario.snapshot : metadata.snapshot;
  const catalogResponse = await fetch(`data/catalog/${requestedSnapshot}`, { cache: "no-store" });
  if (!catalogResponse.ok) throw new Error(`Archived catalog snapshot “${requestedSnapshot}” is unavailable (${catalogResponse.status}); the current catalog was not substituted.`);
  catalog = await catalogResponse.json();
  if ((!sharedScenario && catalog.length !== metadata.payload_count) || catalog.some(row => row.OBJECT_TYPE !== "PAYLOAD")) throw new Error("Catalog validation failed: count or object type mismatch");
  if (analysisMetadata.catalog_snapshot !== requestedSnapshot || analysisMetadata.processed_count !== catalog.length) throw new Error("Analysis metadata validation failed: archived snapshot or count mismatch");
  renderIndexByCatalogId = new Map(catalog.map((row, index) => [String(row.NORAD_CAT_ID), index]));
  if (renderIndexByCatalogId.size !== catalog.length) throw new Error("Catalog validation failed: duplicate stable payload identifiers");
  catalogSatrecs = catalog.map(row => satellite.json2satrec(row));
  if (catalogSatrecs.length !== catalog.length) throw new Error("Catalog validation failed: SGP4 record count mismatch");
  await initializePromptWorker();
  visualOrbits = catalog.map(row => {
    const meanMotion = Number(row.MEAN_MOTION) * Math.PI * 2 / 86400;
    return { epochMs: Date.parse(row.EPOCH), meanMotion, semiMajor: Math.cbrt(MU_EARTH_KM3_S2 / (meanMotion * meanMotion)), eccentricity: Number(row.ECCENTRICITY), inclination: THREE.MathUtils.degToRad(Number(row.INCLINATION)), raan: THREE.MathUtils.degToRad(Number(row.RA_OF_ASC_NODE)), argPerigee: THREE.MathUtils.degToRad(Number(row.ARG_OF_PERICENTER)), meanAnomaly: THREE.MathUtils.degToRad(Number(row.MEAN_ANOMALY)) };
  });
  if (visualOrbits.some(orbit => !Object.values(orbit).every(Number.isFinite))) throw new Error("Catalog validation failed: invalid visual orbit elements");
  const searchResponse = await fetch("data/catalog/catalog-search-index.json", { cache: "no-store" });
  if (!searchResponse.ok) throw new Error(`Catalog search-index request failed: ${searchResponse.status}`);
  catalogSearch = await searchResponse.json();
  const snapshotTimestamp = requestedSnapshot.match(/(\d{8}T\d{6}Z)/)?.[1] || metadata.retrieval_utc;
  catalogEpoch = new Date(snapshotTimestamp.replace(/^(\d{4})(\d{2})(\d{2})T(\d{2})(\d{2})(\d{2})Z$/, "$1-$2-$3T$4:$5:$6Z"));
  catalogMetadata = { ...metadata, snapshot: requestedSnapshot, retrieval_utc: snapshotTimestamp };
  renderCatalog();
  setTimeout(() => {
    if (sharedScenario) {
      if (!carrierOrbitIsValid(sharedScenario.orbit)) { showLoadError(new Error("Shared carrier orbit violates the 100 km minimum-perigee constraint.")); return; }
      Object.assign(carrierOrbit, sharedScenario.orbit); carrierBaseOrbit = { ...carrierOrbit }; carrierBaseLabel = "Shared scenario"; carrierBaseCatalogId = sharedScenario.carrierId;
      simulationSeconds = (sharedScenario.epoch.getTime() - catalogEpoch.getTime()) / 1000;
      selectedAnalysisThreshold = sharedScenario.threshold;
      document.querySelectorAll("[data-yield]").forEach(button => button.classList.toggle("activeYield", Number(button.dataset.yield) === sharedScenario.yieldKt));
      renderCarrier(); makeCarrierTrajectory(false); syncOrbitControls(); updateSatellitePositions(true); setAppState(APP_STATES.PAUSED);
      setTimeout(() => beginDetonationSequence(), 350);
    } else {
      chooseRepresentativeOrbit(false); renderCarrier(); presentCarrierOrbit(false); setTimeout(() => startYieldPuff(100), 1350); setTimeout(() => setAppState(APP_STATES.RUNNING), 2350);
    }
  }, 850);
}

function showLoadError(error) {
  const status = document.getElementById("status"); status.style.display = "block"; status.className = "loadError"; status.textContent = error.message;
  setAppState(APP_STATES.LOADING);
}

function getUiBounds() { const r = document.getElementById("ui").getBoundingClientRect(); return { right: Math.min(innerWidth, Math.max(0, r.right)) }; }
function applyViewOffset(targetCamera) { const width = Math.max(1, innerWidth), height = Math.max(1, innerHeight), shift = getUiBounds().right / 2; targetCamera.setViewOffset(width, height, -shift, 0, width, height); targetCamera.updateProjectionMatrix(); }
function apply3DViewOffset() { applyViewOffset(camera); }
function geographicNorthUp(position, target, previousValidUp = camera.up) {
  const forward = target.clone().sub(position).normalize();
  const north = EARTH_NORTH.clone().projectOnPlane(forward);
  if (north.lengthSq() > 1e-5) return north.normalize();
  const stableFallback = previousValidUp.clone().projectOnPlane(forward);
  if (stableFallback.lengthSq() > 1e-5) return stableFallback.normalize();
  return new THREE.Vector3(0, 0, 1).projectOnPlane(forward).normalize();
}
function beginCameraTransition(position, target, up, duration = 1250, motion = "linear") {
  const transition = { startedAt: performance.now(), duration, motion, fromPosition: camera.position.clone(), toPosition: position.clone(), fromTarget: controls.target.clone(), toTarget: target.clone(), toUp: up.clone(), previousValidUp: geographicNorthUp(camera.position, controls.target, up) };
  if (motion === "azimuthal") {
    const fromOffset = camera.position.clone().sub(controls.target), toOffset = position.clone().sub(target);
    transition.fromRadius = fromOffset.length(); transition.toRadius = toOffset.length();
    transition.fromElevation = Math.asin(THREE.MathUtils.clamp(fromOffset.y / transition.fromRadius, -1, 1)); transition.toElevation = Math.asin(THREE.MathUtils.clamp(toOffset.y / transition.toRadius, -1, 1));
    transition.fromAzimuth = Math.atan2(fromOffset.z, fromOffset.x); const targetAzimuth = Math.atan2(toOffset.z, toOffset.x);
    transition.azimuthDelta = Math.atan2(Math.sin(targetAzimuth - transition.fromAzimuth), Math.cos(targetAzimuth - transition.fromAzimuth));
  }
  if (motion === "azimuthal") window.__generatedOrbitPresentationAudit = { motion, minimumNorthAlignment: 1, maximumElevationDeltaRadians: Math.abs(transition.toElevation - transition.fromElevation), azimuthDeltaRadians: Math.abs(transition.azimuthDelta) };
  cameraTransition = transition;
}
function updateCameraTransition(now) {
  if (!cameraTransition) return;
  const transition = cameraTransition, raw = Math.min(1, (now - transition.startedAt) / transition.duration), eased = raw * raw * (3 - 2 * raw);
  controls.target.lerpVectors(transition.fromTarget, transition.toTarget, eased);
  if (transition.motion === "azimuthal") {
    const radius = THREE.MathUtils.lerp(transition.fromRadius, transition.toRadius, eased), elevation = THREE.MathUtils.lerp(transition.fromElevation, transition.toElevation, eased), azimuth = transition.fromAzimuth + transition.azimuthDelta * eased, horizontal = radius * Math.cos(elevation);
    camera.position.copy(controls.target).add(new THREE.Vector3(horizontal * Math.cos(azimuth), radius * Math.sin(elevation), horizontal * Math.sin(azimuth)));
  } else camera.position.lerpVectors(transition.fromPosition, transition.toPosition, eased);
  const desiredUp = geographicNorthUp(camera.position, controls.target, transition.previousValidUp); transition.previousValidUp.copy(desiredUp);
  if (transition.motion === "azimuthal") {
    const forward = controls.target.clone().sub(camera.position).normalize(), north = EARTH_NORTH.clone().projectOnPlane(forward).normalize();
    window.__generatedOrbitPresentationAudit.minimumNorthAlignment = Math.min(window.__generatedOrbitPresentationAudit.minimumNorthAlignment, desiredUp.dot(north));
  }
  camera.up.copy(desiredUp); camera.lookAt(controls.target);
  if (raw >= 1) cameraTransition = null;
}
function setFullEarthView() { cameraTransition = null; const focus = latLonToVector3(35, 103); camera.position.copy(focus.multiplyScalar(4.1)); controls.target.set(0, 0, 0); camera.up.copy(geographicNorthUp(camera.position, controls.target)); camera.lookAt(controls.target); controls.update(); apply3DViewOffset(); if(points) points.material.uniforms.focusScale.value=1; }
function beginGlobalHomeTransition(duration = 3600) {
  const position = latLonToVector3(35, 103).multiplyScalar(4.1), target = new THREE.Vector3(), up = geographicNorthUp(position, target, camera.up);
  beginCameraTransition(position, target, up, duration, "azimuthal");
  apply3DViewOffset();
  if (points) points.material.uniforms.focusScale.value = 1;
  window.__resultsHomeTransitionAudit = { startedAtSimulationSeconds: simulationSeconds, durationMs: duration, target: target.toArray(), position: position.toArray(), northUp: true };
}
function beginResultsGlobeTransition(duration = 3600) {
  const siteDirection = blastResults?.burstScene?.clone().normalize() || latLonToVector3(35, 103), position = siteDirection.multiplyScalar(4.1), target = new THREE.Vector3(), up = geographicNorthUp(position, target, camera.up);
  beginCameraTransition(position, target, up, duration, "azimuthal"); apply3DViewOffset();
  if (points) points.material.uniforms.focusScale.value = 1;
  window.__resultsHomeTransitionAudit = { startedAtSimulationSeconds: simulationSeconds, durationMs: duration, target: target.toArray(), position: position.toArray(), detonationSiteVisible: true, northUp: true };
}
function centerPointInFullViewport(position, target, up, point) {
  const testCamera = new THREE.PerspectiveCamera(camera.fov, innerWidth / Math.max(1, innerHeight), camera.near, camera.far);
  testCamera.zoom = camera.zoom; testCamera.position.copy(position); testCamera.up.copy(up); testCamera.lookAt(target); applyViewOffset(testCamera);
  for (let pass = 0; pass < 2; pass++) {
    testCamera.updateMatrixWorld(true);
    const projected = point.clone().project(testCamera), cameraSpace = point.clone().applyMatrix4(testCamera.matrixWorldInverse), depth = Math.max(.01, -cameraSpace.z);
    const halfHeight = depth * Math.tan(THREE.MathUtils.degToRad(testCamera.fov * .5)) / testCamera.zoom, halfWidth = halfHeight * testCamera.aspect;
    const right = new THREE.Vector3(1, 0, 0).applyQuaternion(testCamera.quaternion), screenUp = new THREE.Vector3(0, 1, 0).applyQuaternion(testCamera.quaternion);
    const shift = right.multiplyScalar(projected.x * halfWidth).addScaledVector(screenUp, projected.y * halfHeight);
    position.add(shift); target.add(shift); testCamera.position.copy(position); testCamera.lookAt(target);
  }
  return { position, target, up };
}

function calculateDetonationCameraState(burstPosition) {
  const burst = burstPosition.clone(), radius = burst.length(), radial = burst.clone().normalize();
  let tangent = carrierPosition(simulationSeconds + 2).sub(burst).projectOnPlane(radial);
  if (tangent.lengthSq() < .0001) tangent = new THREE.Vector3(0, 1, 0).projectOnPlane(radial);
  tangent.normalize();

  function composeAt(cameraRadius, angle) {
    const cameraRadial = radial.clone().multiplyScalar(Math.cos(angle)).addScaledVector(tangent, Math.sin(angle)).normalize();
    const position = cameraRadial.multiplyScalar(cameraRadius), forward = burst.clone().sub(position).normalize();
    const up = geographicNorthUp(position, burst, radial);
    const target = position.clone().addScaledVector(forward, DETONATION_CAMERA_RANGE_EARTH_RADII);
    return centerPointInFullViewport(position, target, up, burst);
  }

  function solveAt(cameraRadius) {
    let low = 0, high = Math.acos(Math.min(.999, radius / cameraRadius)), state = null;
    for (let i = 0; i < 48; i++) {
      const angle = (low + high) / 2; state = composeAt(cameraRadius, angle);
      const earthDirection = state.position.clone().negate().normalize(), burstDirection = burst.clone().sub(state.position).normalize();
      const separation = Math.acos(THREE.MathUtils.clamp(earthDirection.dot(burstDirection), -1, 1));
      const earthAngularRadius = Math.asin(Math.min(.999, 1 / state.position.length()));
      if (separation / earthAngularRadius < DETONATION_APPARENT_RADIUS_FRACTION) low = angle; else high = angle;
    }
    return composeAt(cameraRadius, (low + high) / 2);
  }

  let cameraRadius = Math.max(DETONATION_CAMERA_RANGE_EARTH_RADII, radius + 1.15), state = solveAt(cameraRadius);
  const effectHalfAngle = THREE.MathUtils.degToRad(camera.fov * .5 * DETONATION_EFFECT_FRAME_FRACTION), requiredEffectDistance = blastFinalScale / Math.sin(effectHalfAngle), currentEffectDistance = state.position.distanceTo(burst);
  if (currentEffectDistance < requiredEffectDistance) { cameraRadius += (requiredEffectDistance - currentEffectDistance) * 1.08; state = solveAt(cameraRadius); }
  return state;
}

function setDetonationView(burstPosition, duration = 1450) {
  apply3DViewOffset();
  const state = calculateDetonationCameraState(burstPosition);
  beginCameraTransition(state.position, state.target, state.up, duration);
}
function refreshDetonationViewForLayout() {
  const burst = blastShell?.position || detonationSequence?.burstScene;
  if (!burst || (appState !== APP_STATES.COUNTDOWN && appState !== APP_STATES.DETONATION && appState !== APP_STATES.RESULTS)) return;
  const state = calculateDetonationCameraState(burst);
  if (cameraTransition) { cameraTransition.toPosition.copy(state.position); cameraTransition.toTarget.copy(state.target); cameraTransition.toUp.copy(state.up); }
  else { camera.position.copy(state.position); controls.target.copy(state.target); camera.up.copy(geographicNorthUp(camera.position, controls.target, camera.up)); camera.lookAt(controls.target); controls.update(); }
}
function suspendCarrierTracking(delay = CARRIER_TRACKING_RESUME_DELAY_MS) { carrierTrackingSuppressedUntil = Math.max(carrierTrackingSuppressedUntil, performance.now() + delay); }
controls.addEventListener("start", () => { carrierTrackingInteracting = true; cameraTransition = null; });
controls.addEventListener("end", () => { carrierTrackingInteracting = false; suspendCarrierTracking(); });
function zoomCamera(factor) { suspendCarrierTracking(); const direction = camera.position.clone().sub(controls.target).multiplyScalar(factor); camera.position.copy(controls.target.clone().add(direction)); controls.update(); }
document.getElementById("zoomInBtn").onclick = () => zoomCamera(.82); document.getElementById("zoomOutBtn").onclick = () => zoomCamera(1.22);
document.getElementById("viewToggleBtn").onclick = () => { suspendCarrierTracking(5000); beginGlobalHomeTransition(1200); };
document.getElementById("panelToggleBtn").onclick = event => { const collapsed = document.body.classList.toggle("uiCollapsed"); event.currentTarget.textContent = collapsed ? "›" : "‹"; apply3DViewOffset(); refreshDetonationViewForLayout(); setTimeout(() => { apply3DViewOffset(); refreshDetonationViewForLayout(); }, 300); };

const ORBIT_SLIDER_IDS = ["semiMajorSlider", "eccentricitySlider", "inclinationSlider", "raanSlider", "argPerigeeSlider", "anomalySlider"];
let anomalyEditing = false;

function configurationLocked() { return appState === APP_STATES.LOADING || appState === APP_STATES.COUNTDOWN || appState === APP_STATES.DETONATION || appState === APP_STATES.RESULTS; }
function thresholdIsInteractive() { return appState === APP_STATES.DETONATION || appState === APP_STATES.RESULTS; }
function setAppState(nextState) {
  if (nextState !== APP_STATES.LOADING && window.__visualizationStartupTimer) {
    clearTimeout(window.__visualizationStartupTimer);
    window.__visualizationStartupTimer = null;
  }
  appState = nextState; isPlaying = nextState === APP_STATES.RUNNING;
  controls.enabled = nextState !== APP_STATES.COUNTDOWN;
  document.body.dataset.appState = nextState;
  document.body.dataset.scenarioLocked = String(configurationLocked());
  if (nextState === APP_STATES.LOADING || nextState === APP_STATES.COUNTDOWN || nextState === APP_STATES.DETONATION || nextState === APP_STATES.RESULTS) orbitPresentationResumePending = false;
  if (nextState !== APP_STATES.RUNNING && carrierSprite) { const scale = carrierSprite.userData.baseScale; carrierSprite.scale.set(scale, scale, 1); carrierPulseStartedAt = null; }
  const locked = configurationLocked();
  ["yieldControlGroup", "carrierControlGroup"].forEach(id => { const group = document.getElementById(id); group.disabled = locked; group.setAttribute("aria-disabled", String(locked)); });
  document.getElementById("randomOrbitBtn").disabled = locked;
  document.getElementById("orbitSearch").disabled = locked;
  document.getElementById("orbitEditorToggle").disabled = locked;
  ORBIT_SLIDER_IDS.forEach(id => { document.getElementById(id).disabled = locked; });
  document.querySelectorAll("[data-yield]").forEach(button => { button.disabled = locked; });
  document.getElementById("detonateBtn").disabled = nextState === APP_STATES.LOADING || nextState === APP_STATES.COUNTDOWN;
  const resultsInteractive = nextState === APP_STATES.RESULTS;
  const thresholdInteractive = nextState === APP_STATES.DETONATION || resultsInteractive;
  ["resultsPlayBtn", "resultsTimelineSlider", "resultsSpeedDownBtn", "resultsSpeedUpBtn", "resultsDisclosureBtn", "copyShareLinkBtn", "scenarioInfoBtn", "timingFleetA", "timingFleetB", "timingAnalyzeBtn"].forEach(id => { document.getElementById(id).disabled = !resultsInteractive; });
  document.querySelectorAll(".analysisBreakdownButton").forEach(button => { button.disabled = !resultsInteractive; });
  document.getElementById("fluenceDensityChart").setAttribute("aria-disabled", String(!thresholdInteractive));
  document.getElementById("clearDrilldownsBtn").disabled = !resultsInteractive || !hasActiveDrilldown();
  if (!resultsInteractive) closeScenarioInfo();
  if (locked) closeSearchResults();
}

function wrapDegrees(radians) { return ((THREE.MathUtils.radToDeg(radians) % 360) + 360) % 360; }
function carrierTrueAnomalyAt(seconds) {
  const e = carrierElements(), eccentricAnomaly0 = 2 * Math.atan2(Math.sqrt(1 - e.eccentricity) * Math.sin(e.epochAnomaly / 2), Math.sqrt(1 + e.eccentricity) * Math.cos(e.epochAnomaly / 2));
  const meanAnomaly = eccentricAnomaly0 - e.eccentricity * Math.sin(eccentricAnomaly0) + Math.sqrt(MU_EARTH_KM3_S2 / Math.pow(e.semiMajor, 3)) * seconds;
  const eccentricAnomaly = solveEccentricAnomaly(meanAnomaly, e.eccentricity);
  return 2 * Math.atan2(Math.sqrt(1 + e.eccentricity) * Math.sin(eccentricAnomaly / 2), Math.sqrt(1 - e.eccentricity) * Math.cos(eccentricAnomaly / 2));
}
function setCarrierTrueAnomalyNow(trueAnomaly) {
  const e = carrierOrbit.eccentricity, eccentricNow = 2 * Math.atan2(Math.sqrt(1 - e) * Math.sin(trueAnomaly / 2), Math.sqrt(1 + e) * Math.cos(trueAnomaly / 2)), meanNow = eccentricNow - e * Math.sin(eccentricNow), meanMotion = Math.sqrt(MU_EARTH_KM3_S2 / Math.pow(carrierOrbit.semiMajor, 3)), meanEpoch = meanNow - meanMotion * simulationSeconds, eccentricEpoch = solveEccentricAnomaly(meanEpoch, e);
  carrierOrbit.epochAnomaly = 2 * Math.atan2(Math.sqrt(1 + e) * Math.sin(eccentricEpoch / 2), Math.sqrt(1 - e) * Math.cos(eccentricEpoch / 2));
}

function syncOrbitControls(includeAnomaly = true) {
  const semiMajor = document.getElementById("semiMajorSlider"); if (carrierOrbit.semiMajor > Number(semiMajor.max)) semiMajor.max = Math.ceil(carrierOrbit.semiMajor / 1000) * 1000;
  semiMajor.min = Math.ceil((EARTH_RADIUS_KM + MIN_CARRIER_PERIGEE_KM) / (1 - carrierOrbit.eccentricity));
  semiMajor.value = carrierOrbit.semiMajor; document.getElementById("semiMajorValue").textContent = `${Math.round(carrierOrbit.semiMajor).toLocaleString()} km`;
  const eccentricity = document.getElementById("eccentricitySlider"); eccentricity.max = Math.max(0, 1 - (EARTH_RADIUS_KM + MIN_CARRIER_PERIGEE_KM) / carrierOrbit.semiMajor); eccentricity.value = carrierOrbit.eccentricity; document.getElementById("eccentricityValue").textContent = carrierOrbit.eccentricity.toFixed(3);
  document.getElementById("inclinationSlider").value = THREE.MathUtils.radToDeg(carrierOrbit.inclination); document.getElementById("inclinationValue").textContent = `${THREE.MathUtils.radToDeg(carrierOrbit.inclination).toFixed(1)}°`;
  document.getElementById("raanSlider").value = wrapDegrees(carrierOrbit.raan); document.getElementById("raanValue").textContent = `${wrapDegrees(carrierOrbit.raan).toFixed(1)}°`;
  document.getElementById("argPerigeeSlider").value = wrapDegrees(carrierOrbit.argPerigee); document.getElementById("argPerigeeValue").textContent = `${wrapDegrees(carrierOrbit.argPerigee).toFixed(1)}°`;
  if (includeAnomaly) { const anomaly = wrapDegrees(carrierTrueAnomalyAt(simulationSeconds)); document.getElementById("anomalySlider").value = anomaly; document.getElementById("anomalyValue").textContent = `${anomaly.toFixed(1)}°`; }
  const altitude = Math.round(carrierOrbit.semiMajor - EARTH_RADIUS_KM).toLocaleString(), inclination = THREE.MathUtils.radToDeg(carrierOrbit.inclination).toFixed(1);
  document.getElementById("selectedOrbitSummary").textContent = `${altitude} km altitude · ${inclination}° inclination`;
}

function presentCarrierOrbit(resumeAfter = true) {
  const priorState = appState;
  if (priorState === APP_STATES.RUNNING) { orbitPresentationResumePending = resumeAfter; setAppState(APP_STATES.PAUSED); }
  if (orbitPresentationTimer) clearTimeout(orbitPresentationTimer);
  const anomaly = carrierTrueAnomalyAt(simulationSeconds), radial = carrierPosition(simulationSeconds).normalize(), p0 = carrierPlanePoint(anomaly, true), p1 = carrierPlanePoint(anomaly + .04, true), normal = p0.clone().cross(p1).normalize();
  if (normal.dot(camera.position) < 0) normal.negate();
  const planned = pendingCarrierPresentation; pendingCarrierPresentation = null;
  const viewDirection = planned ? planned.direction.clone() : radial.multiplyScalar(.86).addScaledVector(normal, .51).normalize(), position = viewDirection.multiplyScalar(planned?.range || Math.max(4.0, carrierPosition(simulationSeconds).length() + 2.35));
  const up = geographicNorthUp(position, new THREE.Vector3(), normal);
  beginCameraTransition(position, new THREE.Vector3(), up, 1150, planned ? "azimuthal" : "linear"); apply3DViewOffset();
  if (resumeAfter && priorState === APP_STATES.RUNNING) orbitPresentationTimer = setTimeout(() => { orbitPresentationTimer = null; if (appState === APP_STATES.PAUSED) { orbitPresentationResumePending = false; setAppState(APP_STATES.RUNNING); } }, 1500);
}

function updateCarrierTracking(now, dt) {
  if (appState !== APP_STATES.RUNNING || !carrierSprite || cameraTransition || carrierTrackingInteracting || now < carrierTrackingSuppressedUntil) return;
  const burst = carrierSprite.position.clone(), radial = burst.clone().normalize(), future = carrierPosition(simulationSeconds + 30), tangent = future.sub(burst).projectOnPlane(radial);
  if (tangent.lengthSq() < 1e-10) return;
  tangent.normalize();
  let normal = new THREE.Vector3().crossVectors(radial, tangent).normalize();
  const currentDirection = camera.position.clone().sub(controls.target).normalize();
  if (normal.dot(currentDirection) < 0) normal.negate();
  const desiredDirection = radial.clone().multiplyScalar(.86).addScaledVector(normal, .51).normalize();
  const desiredUp = geographicNorthUp(desiredDirection.clone().multiplyScalar(camera.position.distanceTo(controls.target)), new THREE.Vector3(), normal);

  const step = Math.min(dt, .05), directionBlend = 1 - Math.exp(-3.0 * step), targetBlend = 1 - Math.exp(-1.8 * step), range = camera.position.distanceTo(controls.target);
  const nextTarget = controls.target.clone().lerp(new THREE.Vector3(), targetBlend), nextDirection = currentDirection.lerp(desiredDirection, directionBlend).normalize();
  controls.target.copy(nextTarget); camera.position.copy(nextTarget).addScaledVector(nextDirection, range); camera.up.copy(geographicNorthUp(camera.position, controls.target, desiredUp)); camera.lookAt(controls.target);
}

function setCarrierBase(orbit, label, focusCamera = true) {
  if (!carrierOrbitIsValid(orbit)) { showOrbitConstraint(true); return false; }
  Object.assign(carrierOrbit, orbit); carrierBaseOrbit = { ...carrierOrbit }; carrierBaseLabel = label;
  showOrbitConstraint(false);
  carrierTrackingSuppressedUntil = 0;
  syncOrbitControls(); makeCarrierTrajectory();
  document.getElementById("orbitEditorBody").hidden = true; document.getElementById("orbitEditorToggle").setAttribute("aria-expanded", "false"); document.getElementById("orbitEditorToggle").textContent = "Adjust parameters ▾";
  if (focusCamera) requestAnimationFrame(() => presentCarrierOrbit(true));
  return true;
}

function setCarrierFromVisualOrbit(index) {
  const orbit = visualOrbits[index], elapsed = (catalogEpoch.getTime() - orbit.epochMs) / 1000, meanAnomaly = orbit.meanAnomaly + orbit.meanMotion * elapsed;
  const eccentricAnomaly = solveEccentricAnomaly(meanAnomaly, orbit.eccentricity);
  const trueAnomaly = 2 * Math.atan2(Math.sqrt(1 + orbit.eccentricity) * Math.sin(eccentricAnomaly / 2), Math.sqrt(1 - orbit.eccentricity) * Math.cos(eccentricAnomaly / 2));
  const label = `${catalog[index].OBJECT_NAME} (${catalog[index].OBJECT_ID})`;
  if (!setCarrierBase({ semiMajor: orbit.semiMajor, eccentricity: orbit.eccentricity, inclination: orbit.inclination, raan: orbit.raan, argPerigee: orbit.argPerigee, epochAnomaly: trueAnomaly }, label)) return;
  carrierBaseCatalogId = String(catalog[index].NORAD_CAT_ID);
  document.getElementById("orbitSearch").value = label;
  closeSearchResults();
}

function chooseRepresentativeOrbit(focusCamera = true) {
  const pool = visualOrbits.map((orbit, index) => ({ orbit, index })).filter(({ orbit }) => {
    const altitude = orbit.semiMajor - EARTH_RADIUS_KM;
    return altitude >= 150 && altitude <= 4000 && orbit.eccentricity < .25 && carrierOrbitIsValid(orbit);
  });
  if (!pool.length) return;

  const meanA = pool.reduce((sum, item) => sum + item.orbit.semiMajor, 0) / pool.length;
  const meanI = pool.reduce((sum, item) => sum + item.orbit.inclination, 0) / pool.length;
  const sigmaA = Math.sqrt(pool.reduce((sum, item) => sum + Math.pow(item.orbit.semiMajor - meanA, 2), 0) / pool.length) || 1;
  const sigmaI = Math.sqrt(pool.reduce((sum, item) => sum + Math.pow(item.orbit.inclination - meanI, 2), 0) / pool.length) || 1;

  const currentDirection = camera.position.clone().sub(controls.target).normalize(), currentElevation = THREE.MathUtils.clamp(currentDirection.y, -.72, .72), horizontalScale = Math.sqrt(1 - currentElevation * currentElevation), currentAzimuth = Math.atan2(currentDirection.z, currentDirection.x);
  let selected = null;
  for (let attempt = 0; attempt < 180; attempt++) {
    const candidate = pool[Math.floor(Math.random() * pool.length)];
    const zA = (candidate.orbit.semiMajor - meanA) / sigmaA;
    const zI = (candidate.orbit.inclination - meanI) / sigmaI;
    if (Math.random() > Math.exp(-.5 * (zA * zA + zI * zI))) continue;
    const anomaly = Math.random() * Math.PI * 2, radial = orbitPlanePoint(candidate.orbit, anomaly, true).normalize(), horizontal = Math.hypot(radial.x, radial.z);
    if (horizontal < .12) continue;
    const direction = new THREE.Vector3(radial.x / horizontal * horizontalScale, currentElevation, radial.z / horizontal * horizontalScale).normalize();
    const visibility = direction.dot(radial), p0 = orbitPlanePoint(candidate.orbit, anomaly, true), p1 = orbitPlanePoint(candidate.orbit, anomaly + .035, true), normal = p0.clone().cross(p1).normalize(), planeLegibility = Math.abs(normal.dot(direction));
    const desiredAzimuth = Math.atan2(direction.z, direction.x), azimuthTravel = Math.abs(Math.atan2(Math.sin(desiredAzimuth - currentAzimuth), Math.cos(desiredAzimuth - currentAzimuth)));
    const score = azimuthTravel * .45 + Math.max(0, .62 - visibility) * 8 + Math.max(0, .2 - planeLegibility) * 4 + .08 * (zA * zA + zI * zI);
    if (!selected || score < selected.score) selected = { ...candidate, anomaly, direction, score };
  }
  if (!selected) return;
  const source = selected.orbit;
  pendingCarrierPresentation = { direction: selected.direction, range: THREE.MathUtils.clamp(Math.max(camera.position.distanceTo(controls.target), source.semiMajor * (1 + source.eccentricity) * SCALE + 2.15), 3.8, 5.3), score: selected.score };
  setCarrierBase({ semiMajor: source.semiMajor, eccentricity: source.eccentricity, inclination: source.inclination, raan: source.raan, argPerigee: source.argPerigee, epochAnomaly: selected.anomaly }, "Representative random orbit", focusCamera);
  carrierBaseCatalogId = null;
  document.getElementById("orbitSearch").value = "";
  closeSearchResults();
}

document.getElementById("randomOrbitBtn").onclick = () => chooseRepresentativeOrbit(true);
document.getElementById("orbitEditorToggle").onclick = event => { const body = document.getElementById("orbitEditorBody"), opening = body.hidden; body.hidden = !opening; event.currentTarget.setAttribute("aria-expanded", String(opening)); event.currentTarget.textContent = opening ? "Close parameters ▴" : "Adjust parameters ▾"; };

ORBIT_SLIDER_IDS.forEach(id => document.getElementById(id).addEventListener("input", event => {
  if (configurationLocked()) return;
  const value = Number(event.target.value), currentAnomaly = carrierTrueAnomalyAt(simulationSeconds);
  let constrained = false;
  if (id === "semiMajorSlider") { const minimum = (EARTH_RADIUS_KM + MIN_CARRIER_PERIGEE_KM) / (1 - carrierOrbit.eccentricity), accepted = Math.max(value, minimum); carrierOrbit.semiMajor = accepted; event.target.value = accepted; constrained = accepted !== value; }
  if (id === "eccentricitySlider") { const maximum = Math.max(0, 1 - (EARTH_RADIUS_KM + MIN_CARRIER_PERIGEE_KM) / carrierOrbit.semiMajor), accepted = Math.min(value, maximum); carrierOrbit.eccentricity = accepted; event.target.value = accepted; constrained = accepted !== value; }
  if (id === "inclinationSlider") carrierOrbit.inclination = THREE.MathUtils.degToRad(value);
  if (id === "raanSlider") carrierOrbit.raan = THREE.MathUtils.degToRad(value);
  if (id === "argPerigeeSlider") carrierOrbit.argPerigee = THREE.MathUtils.degToRad(value);
  if (id === "anomalySlider") setCarrierTrueAnomalyNow(THREE.MathUtils.degToRad(value));
  else setCarrierTrueAnomalyNow(currentAnomaly);
  showOrbitConstraint(constrained || carrierPerigeeKm() < MIN_CARRIER_PERIGEE_KM + .5);
  carrierBaseOrbit = { ...carrierOrbit }; carrierBaseCatalogId = null; carrierBaseLabel = carrierBaseLabel.replace(/ · adjusted$/, "") + " · adjusted"; syncOrbitControls(id !== "anomalySlider"); scheduleInteractiveTrajectoryUpdate();
}));
document.getElementById("anomalySlider").addEventListener("pointerdown", () => { anomalyEditing = true; });
addEventListener("pointerup", () => { anomalyEditing = false; });

function positionSearchResults() { const input = document.getElementById("orbitSearch"), results = document.getElementById("orbitSearchResults"); if (!results.classList.contains("open")) return; const rect = input.getBoundingClientRect(), width = Math.min(420, innerWidth - 24), left = Math.max(12, Math.min(rect.left, innerWidth - width - 12)), below = innerHeight - rect.bottom - 12, above = rect.top - 12, useBelow = below >= Math.min(220, above), available = useBelow ? below : above, height = Math.min(320, Math.max(120, available)); results.style.width = `${width}px`; results.style.left = `${left}px`; results.style.top = `${useBelow ? rect.bottom + 6 : Math.max(12, rect.top - height - 6)}px`; results.style.maxHeight = `${height}px`; }
function closeSearchResults() { const results = document.getElementById("orbitSearchResults"); results.classList.remove("open"); results.setAttribute("aria-hidden", "true"); results.innerHTML = ""; }
function openSearchResults() { const results = document.getElementById("orbitSearchResults"), header = document.createElement("div"); header.className = "searchResultsHeader"; header.innerHTML = '<span>Satellite matches</span><button type="button" aria-label="Close search results">×</button>'; header.querySelector("button").onclick = closeSearchResults; results.appendChild(header); results.classList.add("open"); results.setAttribute("aria-hidden", "false"); positionSearchResults(); }

document.getElementById("orbitSearch").addEventListener("input", event => {
  const query = event.target.value.trim().toLowerCase(), results = document.getElementById("orbitSearchResults"); closeSearchResults();
  if (query.length < 2 || configurationLocked()) return;
  openSearchResults();
  const score = row => { const name = row.name.toLowerCase(), cospar = row.cospar.toLowerCase(); if (name === query || cospar === query) return 0; if (name.startsWith(query) || cospar.startsWith(query)) return 1; if (name.split(/\s+/).some(token => token.startsWith(query))) return 2; return 3; };
  catalogSearch.filter(row => row.name.toLowerCase().includes(query) || row.cospar.toLowerCase().includes(query)).map(row => ({ row, score: score(row) })).sort((a, b) => a.score - b.score || Number(a.row.activeIndex === null) - Number(b.row.activeIndex === null) || a.row.name.localeCompare(b.row.name)).slice(0, 7).forEach(({ row }) => { const button = document.createElement("button"); button.textContent = `${row.name} (${row.cospar || "no COSPAR ID"})${row.activeIndex === null ? ` · ${row.decay ? "decayed " + row.decay : "no current GP orbit"}` : ""}`; if (row.activeIndex === null) { button.disabled = true; button.title = "This catalog payload has no current public orbital elements and cannot be used as a present-day carrier orbit."; } else button.onclick = () => setCarrierFromVisualOrbit(row.activeIndex); results.appendChild(button); });
});
document.addEventListener("pointerdown", event => { const results = document.getElementById("orbitSearchResults"), input = document.getElementById("orbitSearch"); if (!results.contains(event.target) && event.target !== input) closeSearchResults(); });
document.addEventListener("keydown", event => { if (event.key === "Escape") closeSearchResults(); });
document.getElementById("ui").addEventListener("scroll", positionSearchResults);

function effectRadiusScene(yieldKt) { return thresholdRadiusMeters(yieldKt, PERMANENT_DAMAGE_THRESHOLD_J_M2) / 1000 * SCALE; }
function hideYieldPreview() { yieldPreviewPuffStartedAt = null; if (!yieldPreview) return; scene.remove(yieldPreview); yieldPreview.traverse(child => { if (child.geometry) child.geometry.dispose(); if (child.material) child.material.dispose(); }); yieldPreview = null; }
function showYieldPreview(yieldKt) {
  if (!carrierSprite || blastShell) return;
  hideYieldPreview();
  yieldPreview = new THREE.Group();
  for (let i = 0; i < 9; i++) { const fraction = .50 + i / 16, baseOpacity = .008 + i * .0015, material = new THREE.MeshBasicMaterial({ color: 0x555555, transparent: true, opacity: baseOpacity, depthTest: true, depthWrite: false, side: THREE.DoubleSide }); material.userData.baseOpacity = baseOpacity; const layer = new THREE.Mesh(new THREE.SphereGeometry(fraction, 32, 22), material); layer.renderOrder = 7; yieldPreview.add(layer); }
  yieldPreview.userData.targetScale = effectRadiusScene(yieldKt); yieldPreview.position.copy(carrierSprite.position); yieldPreview.scale.setScalar(yieldPreview.userData.targetScale); scene.add(yieldPreview);
}
function startYieldPuff(yieldKt) { showYieldPreview(yieldKt); if (!yieldPreview) return; yieldPreviewPuffStartedAt = performance.now(); yieldPreview.scale.setScalar(yieldPreview.userData.targetScale * .08); }

document.querySelectorAll("[data-yield]").forEach(button => {
  button.onclick = () => { document.querySelector(".activeYield").classList.remove("activeYield"); button.classList.add("activeYield"); };
  button.onmouseenter = () => startYieldPuff(Number(button.dataset.yield));
  button.onmouseleave = hideYieldPreview;
  button.onfocus = () => startYieldPuff(Number(button.dataset.yield));
  button.onblur = hideYieldPreview;
});

function sceneToEcfKm(position) { return { x: position.x * EARTH_RADIUS_KM, y: -position.z * EARTH_RADIUS_KM, z: position.y * EARTH_RADIUS_KM }; }
function ecfKmToScene(position) { return new THREE.Vector3(position.x, position.z, -position.y).multiplyScalar(SCALE); }

function propagateCatalogAtDetonation(epoch) {
  const positionsEciKm = new Float64Array(catalog.length * 3), velocitiesEciKmS = new Float64Array(catalog.length * 3), positionsScene = points.geometry.attributes.position.array;
  positionsEciKm.fill(NaN); velocitiesEciKmS.fill(NaN);
  const gmst = satellite.gstime(epoch);
  let validCount = 0;
  for (let index = 0; index < catalogSatrecs.length; index++) {
    const state = satellite.propagate(catalogSatrecs[index], epoch), positionEci = state && state.position, velocityEci = state && state.velocity;
    if (!positionEci || !velocityEci || !Number.isFinite(positionEci.x) || !Number.isFinite(positionEci.y) || !Number.isFinite(positionEci.z) || !Number.isFinite(velocityEci.x) || !Number.isFinite(velocityEci.y) || !Number.isFinite(velocityEci.z)) continue;
    const offset = index * 3;
    positionsEciKm[offset] = positionEci.x; positionsEciKm[offset + 1] = positionEci.y; positionsEciKm[offset + 2] = positionEci.z;
    velocitiesEciKmS[offset] = velocityEci.x; velocitiesEciKmS[offset + 1] = velocityEci.y; velocitiesEciKmS[offset + 2] = velocityEci.z;
    const scenePosition = ecfKmToScene(satellite.eciToEcf(positionEci, gmst));
    positionsScene[offset] = scenePosition.x; positionsScene[offset + 1] = scenePosition.y; positionsScene[offset + 2] = scenePosition.z;
    validCount++;
  }
  points.geometry.attributes.position.needsUpdate = true;
  return { positionsEciKm, velocitiesEciKmS, sceneFrame: new Float32Array(positionsScene), validCount, gmst };
}

function updateResultSatellitePositions() {
  if (!points || !blastResults) return;
  const bracket = Math.floor(resultPlaybackSeconds / PROPAGATION_KEYFRAME_SECONDS) * PROPAGATION_KEYFRAME_SECONDS;
  if (bracket !== resultFrameStart) {
    const reuse = bracket === resultFrameStart + PROPAGATION_KEYFRAME_SECONDS && resultFrame1;
    resultFrameStart = bracket;
    resultFrame0 = reuse ? resultFrame1 : computeResultPopulationFrame(bracket);
    resultFrame1 = computeResultPopulationFrame(bracket + PROPAGATION_KEYFRAME_SECONDS);
  }
  const alpha = (resultPlaybackSeconds - resultFrameStart) / PROPAGATION_KEYFRAME_SECONDS, positions = points.geometry.attributes.position.array;
  for (let sourceIndex = 0; sourceIndex < resultPlaybackCatalogIds.length; sourceIndex++) {
    const renderIndex = renderIndexByCatalogId.get(resultPlaybackCatalogIds[sourceIndex]); if (renderIndex === undefined) continue;
    const sourceOffset = sourceIndex * 3, renderOffset = renderIndex * 3;
    for (let coordinate = 0; coordinate < 3; coordinate++) { const start = resultFrame0[sourceOffset + coordinate], end = resultFrame1[sourceOffset + coordinate], value = start + (end - start) * alpha; if (Number.isFinite(value)) positions[renderOffset + coordinate] = value; }
  }
  points.geometry.attributes.position.needsUpdate = true;
  carrierSprite.position.copy(carrierPosition(simulationSeconds)); trajectoryGroup.rotation.y = -EARTH_ROTATION_RATE_RAD_PER_SEC * simulationSeconds;
  if (resultsPlaybackPlaying && window.__resultPlaybackIdentityAudit?.before && !window.__resultPlaybackIdentityAudit.after) {
    window.__resultPlaybackIdentityAudit.after = captureRenderedIdentity();
    window.__resultPlaybackIdentityAudit.maxFirstAnimatedPositionDelta = maximumPositionDelta(resultPlaybackContinuityFrame, positions);
    resultPlaybackContinuityFrame = null;
  }
}

function captureRenderedIdentity() {
  if (!points) return { catalogIds: [], visibleIds: [], highlightedIds: [], colorAttachmentChecksum: 0, scaleAttachmentChecksum: 0 };
  const positions = points.geometry.attributes.position.array, colors = points.geometry.attributes.effectColor.array, scales = points.geometry.attributes.effectScale.array, alphas = points.geometry.attributes.effectAlpha.array, catalogIds = [], visibleIds = [], highlightedIds = [];
  let colorAttachmentChecksum = 0, scaleAttachmentChecksum = 0;
  catalog.forEach((row, index) => { const offset = index * 3, id = String(row.NORAD_CAT_ID), finite = [positions[offset], positions[offset + 1], positions[offset + 2]].every(Number.isFinite), weight = Number(row.NORAD_CAT_ID) % 997 + 1; if (finite) catalogIds.push(id); if (finite && alphas[index] > 0) visibleIds.push(id); if (scales[index] > 1.001) highlightedIds.push(id); colorAttachmentChecksum += weight * (colors[offset] * 3 + colors[offset + 1] * 5 + colors[offset + 2] * 7); scaleAttachmentChecksum += weight * scales[index]; });
  return { catalogIds, visibleIds, highlightedIds, colorAttachmentChecksum, scaleAttachmentChecksum };
}

function maximumPositionDelta(before, after) {
  if (!before || !after || before.length !== after.length) return Infinity;
  let maximum = 0;
  for (let index = 0; index < before.length; index += 3) {
    if (![before[index], before[index + 1], before[index + 2], after[index], after[index + 1], after[index + 2]].every(Number.isFinite)) continue;
    maximum = Math.max(maximum, Math.hypot(after[index] - before[index], after[index + 1] - before[index + 1], after[index + 2] - before[index + 2]));
  }
  return maximum;
}

function auditLegacyPlaybackHandoff(exactFrame, independentlyPhasedNextFrame) {
  let maximumDeltaEarthRadii = 0, finiteCount = 0, chordMidpointsInsideEarth = 0;
  for (let index = 0; index < exactFrame.length; index += 3) {
    const values = [exactFrame[index], exactFrame[index + 1], exactFrame[index + 2], independentlyPhasedNextFrame[index], independentlyPhasedNextFrame[index + 1], independentlyPhasedNextFrame[index + 2]];
    if (!values.every(Number.isFinite)) continue;
    finiteCount++;
    maximumDeltaEarthRadii = Math.max(maximumDeltaEarthRadii, Math.hypot(values[3] - values[0], values[4] - values[1], values[5] - values[2]));
    if (Math.hypot((values[0] + values[3]) / 2, (values[1] + values[4]) / 2, (values[2] + values[5]) / 2) < 1) chordMidpointsInsideEarth++;
  }
  window.__legacyPlaybackDiscontinuityAudit = { finiteCount, maximumDeltaEarthRadii, chordMidpointsInsideEarth };
}

function analyticalMetadataFor(catalogId) {
  return analysisMetadata?.entries?.[String(catalogId)] || { categoryCode: "", categoryRaw: "", missionPurpose: "Other / unknown", program: "", constellation: "Other" };
}

function attachAnalyticalMetadata(records) {
  records.forEach(record => Object.assign(record, analyticalMetadataFor(record.catalogId)));
  return records;
}

function prepareBlastResults(burstScene, yieldKt) {
  if (!points) return null;
  const detonationEpoch = new Date(catalogEpoch.getTime() + simulationSeconds * 1000);
  const propagated = propagateCatalogAtDetonation(detonationEpoch);
  const burstEci = satellite.ecfToEci(sceneToEcfKm(burstScene), propagated.gmst), burstEciKm = [burstEci.x, burstEci.y, burstEci.z];
  const result = calculatePromptExposure({ catalog, positionsEciKm: propagated.positionsEciKm, burstEciKm, yieldKt, earthRadiusKm: EARTH_RADIUS_KM }); attachAnalyticalMetadata(result.records);
  const reachedAt = new Float64Array(catalog.length); reachedAt.fill(-1);
  const distanceScene = new Float64Array(catalog.length);
  for (let index = 0; index < result.records.length; index++) distanceScene[index] = result.records[index].distanceKm === null ? Infinity : result.records[index].distanceKm * SCALE;
  resultDetonationSimulationSeconds = simulationSeconds; resultPlaybackSeconds = 0; resultFrameStart = 0; resultFrame0 = propagated.sceneFrame;
  resultPlaybackCatalogIds = catalog.map(row => String(row.NORAD_CAT_ID));
  auditLegacyPlaybackHandoff(resultFrame0, computePopulationFrame(resultDetonationSimulationSeconds + PROPAGATION_KEYFRAME_SECONDS));
  initializeResultVisualStates(propagated.positionsEciKm, propagated.velocitiesEciKmS); resultFrame1 = computeResultPopulationFrame(PROPAGATION_KEYFRAME_SECONDS);
  return {
    ...result,
    detonationEpoch: detonationEpoch.toISOString(),
    yieldKt,
    burstEciKm,
    burstScene: burstScene.clone(),
    positionsEciKm: propagated.positionsEciKm,
    propagatedCount: propagated.validCount,
    distanceScene,
    reachedAt,
    fluenceDomain: [result.summary.minimumPositiveFluence, result.summary.maximumFluence],
    lastHistogramUpdate: 0
  };
}

async function prepareBlastResultsAsync(burstScene, yieldKt, detonationEpoch, detonationSimulationSeconds) {
  const gmst = satellite.gstime(detonationEpoch), burstEci = satellite.ecfToEci(sceneToEcfKm(burstScene), gmst), burstEciKm = [burstEci.x, burstEci.y, burstEci.z];
  const worker = await requestPromptCalculation({ epoch: detonationEpoch.toISOString(), burstEciKm, yieldKt, earthRadiusKm: EARTH_RADIUS_KM });
  const positions = points.geometry.attributes.position.array; positions.set(worker.sceneFrame); points.geometry.attributes.position.needsUpdate = true;
  const reachedAt = new Float64Array(catalog.length); reachedAt.fill(-1); const distanceScene = new Float64Array(catalog.length);
  const records = catalog.map((row, index) => {
    const offset = index * 3, valid = Boolean(worker.propagationValid[index]), distanceKm = valid ? worker.distanceKm[index] : null, earthMasked = valid ? Boolean(worker.earthMasked[index]) : null;
    distanceScene[index] = distanceKm === null ? Infinity : distanceKm * SCALE;
    return { catalogIndex: index, catalogId: String(row.NORAD_CAT_ID), cosparId: row.OBJECT_ID || "", name: row.OBJECT_NAME || "", ownerCode: row.OWNER || "Unknown", missionClassCode: row.GCAT_CLASS || "", missionClass: row.MISSION_CLASS || "Unclassified", missionClasses: row.MISSION_CLASSES || [], gcatMatched: Boolean(row.GCAT_MATCHED), ...analyticalMetadataFor(row.NORAD_CAT_ID), positionEciKm: [worker.positionsEciKm[offset], worker.positionsEciKm[offset + 1], worker.positionsEciKm[offset + 2]], distanceKm, earthMasked, fluenceJm2: valid ? worker.fluenceJm2[index] : null, thresholds: { fangMoricPermanentDamage40Jm2: Boolean(worker.exceeds40[index]) }, propagationValid: valid };
  });
  const result = { model: worker.model, summary: worker.summary, records };
  resultDetonationSimulationSeconds = detonationSimulationSeconds; resultPlaybackSeconds = 0; resultFrameStart = 0; resultPlaybackCatalogIds = catalog.map(row => String(row.NORAD_CAT_ID)); resultFrame0 = worker.sceneFrame; auditLegacyPlaybackHandoff(resultFrame0, computePopulationFrame(resultDetonationSimulationSeconds + PROPAGATION_KEYFRAME_SECONDS)); initializeResultVisualStates(worker.positionsEciKm, worker.velocitiesEciKmS); resultFrame1 = computeResultPopulationFrame(PROPAGATION_KEYFRAME_SECONDS);
  return { ...result, detonationEpoch: detonationEpoch.toISOString(), yieldKt, burstEciKm, burstScene: burstScene.clone(), positionsEciKm: worker.positionsEciKm, propagatedCount: worker.validCount, distanceScene, reachedAt, fluenceDomain: [worker.summary.minimumPositiveFluence, worker.summary.maximumFluence], lastHistogramUpdate: 0 };
}

function normalizedLogFluence(value, domain) {
  if (!(value > 0) || !(domain[0] > 0) || !(domain[1] > domain[0])) return 0;
  return THREE.MathUtils.clamp((Math.log10(value) - Math.log10(domain[0])) / (Math.log10(domain[1]) - Math.log10(domain[0])), 0, 1);
}

const FLUENCE_COLOR_STOPS = Object.freeze([
  Object.freeze({ value: .1, color: "#fff3c4" }),
  Object.freeze({ value: 1, color: "#f6d66f" }),
  Object.freeze({ value: 10, color: "#eaaa00" }),
  Object.freeze({ value: 40, color: "#713617" })
]);

function interpolateHexColor(from, to, fraction) {
  const channel = (hex, shift) => parseInt(hex.slice(1), 16) >> shift & 255, mixed = shift => Math.round(channel(from, shift) + (channel(to, shift) - channel(from, shift)) * fraction);
  return `#${[mixed(16), mixed(8), mixed(0)].map(value => value.toString(16).padStart(2, "0")).join("")}`;
}

// The single application-wide fluence encoding. The visual scale saturates at 40 J/m².
function fluenceColor(value, target = null) {
  const safeValue = Math.max(FLUENCE_COLOR_STOPS[0].value, Number.isFinite(value) ? value : FLUENCE_COLOR_STOPS[0].value);
  let color = FLUENCE_COLOR_STOPS.at(-1).color;
  for (let index = 1; index < FLUENCE_COLOR_STOPS.length; index++) {
    const lower = FLUENCE_COLOR_STOPS[index - 1], upper = FLUENCE_COLOR_STOPS[index];
    if (safeValue <= upper.value) {
      const fraction = THREE.MathUtils.clamp((Math.log10(safeValue) - Math.log10(lower.value)) / (Math.log10(upper.value) - Math.log10(lower.value)), 0, 1);
      color = interpolateHexColor(lower.color, upper.color, fraction); break;
    }
  }
  if (!target) return color;
  target.r = parseInt(color.slice(1, 3), 16) / 255; target.g = parseInt(color.slice(3, 5), 16) / 255; target.b = parseInt(color.slice(5, 7), 16) / 255; return target;
}

const FLUENCE_COLOR_REGRESSION_VALUES = Object.freeze([.1, 1, 10, 40, 100, 1000]);
window.__fluenceColorAudit = FLUENCE_COLOR_REGRESSION_VALUES.map(value => { const color = fluenceColor(value); return { fluenceJm2: value, marker: color, chart: color, statisticAccent: color, selectedThreshold: "#222222", mappedEncodingsIdentical: true }; });

function relativeLuminance(hexColor) {
  const linear = channel => channel <= .04045 ? channel / 12.92 : Math.pow((channel + .055) / 1.055, 2.4);
  return [1, 3, 5].map(offset => linear(parseInt(hexColor.slice(offset, offset + 2), 16) / 255)).reduce((sum, channel, index) => sum + channel * [.2126, .7152, .0722][index], 0);
}

function contrastRatio(first, second) {
  const light = Math.max(relativeLuminance(first), relativeLuminance(second)), dark = Math.min(relativeLuminance(first), relativeLuminance(second));
  return (light + .05) / (dark + .05);
}

function statisticNumberColor(mappedColor) {
  return contrastRatio(mappedColor, STATISTIC_CARD_BACKGROUND) >= LARGE_TEXT_MINIMUM_CONTRAST ? mappedColor : INTERFACE_DARK_TEXT;
}

function formatFluence(value) {
  if (!Number.isFinite(value)) return "—";
  if (value >= 1000 || value < .01) return value.toExponential(1);
  if (value >= 10) return value.toFixed(0);
  return value.toPrecision(2);
}

const COUNTRY_GROUPS = ["United States", "China", "Russia / CIS", "Other"];
const MISSION_PURPOSES = ["Communications", "Earth observation", "Navigation", "Science", "Technology / calibration", "Security / defense", "Human spaceflight", "Other / unknown"];
const CONSTELLATION_GROUPS = ["Starlink", "OneWeb", "Kuiper", "Qianfan", "Flock", "Iridium", "Other"];

function countryGroup(record) {
  if (record.ownerCode === "US") return "United States";
  if (record.ownerCode === "PRC") return "China";
  if (record.ownerCode === "CIS") return "Russia / CIS";
  return "Other";
}

function categoryState(states, key) { return states.get(key) || CATEGORY_STATES.NEUTRAL; }
function hasFocusedCategory(states) { return [...states.values()].some(state => state === CATEGORY_STATES.FOCUS); }
function dimensionAllows(states, key) {
  const state = categoryState(states, key);
  if (state === CATEGORY_STATES.EXCLUDE) return false;
  return !hasFocusedCategory(states) || state === CATEGORY_STATES.FOCUS;
}
function hasActiveDrilldown() { return selectedCountryDrilldowns.size > 0 || selectedMissionDrilldowns.size > 0 || selectedConstellationDrilldowns.size > 0; }
function recordMatchesDrilldowns(record, omittedDimension = null) {
  return (omittedDimension === "country" || dimensionAllows(selectedCountryDrilldowns, countryGroup(record)))
    && (omittedDimension === "mission" || dimensionAllows(selectedMissionDrilldowns, record.missionPurpose))
    && (omittedDimension === "constellation" || dimensionAllows(selectedConstellationDrilldowns, record.constellation));
}

function countDistributionModel(result, revealedOnly = false) {
  const [minimum, maximum] = result.fluenceDomain, logMinimum = Math.log10(minimum), logMaximum = Math.log10(maximum), counts = new Float64Array(COUNT_DISTRIBUTION_INTERVALS);
  let populationCount = 0;
  result.records.forEach(record => {
    if (record.earthMasked || !record.propagationValid || !(record.fluenceJm2 > 0) || (revealedOnly && result.reachedAt[record.catalogIndex] < 0)) return;
    const fraction = THREE.MathUtils.clamp((Math.log10(record.fluenceJm2) - logMinimum) / (logMaximum - logMinimum), 0, 1), index = Math.min(COUNT_DISTRIBUTION_INTERVALS - 1, Math.floor(fraction * COUNT_DISTRIBUTION_INTERVALS));
    counts[index]++; populationCount++;
  });
  const samples = [];
  for (let index = 0; index < COUNT_DISTRIBUTION_INTERVALS; index++) {
    let weightedCount = 0, weightTotal = 0;
    for (let neighbor = Math.max(0, index - 5); neighbor <= Math.min(COUNT_DISTRIBUTION_INTERVALS - 1, index + 5); neighbor++) { const z = (index - neighbor) / COUNT_SMOOTHING_SIGMA_INTERVALS, weight = Math.exp(-.5 * z * z); weightedCount += counts[neighbor] * weight; weightTotal += weight; }
    samples.push({ x: logMinimum + (index + .5) / COUNT_DISTRIBUTION_INTERVALS * (logMaximum - logMinimum), count: weightTotal ? weightedCount / weightTotal : 0 });
  }
  return { samples, populationCount, intervalLog10Width: (logMaximum - logMinimum) / COUNT_DISTRIBUTION_INTERVALS };
}

function thresholdPopulation() { return blastResults ? blastResults.records.filter(record => record.propagationValid && !record.earthMasked && record.fluenceJm2 >= selectedAnalysisThreshold) : []; }

const DENSITY_CHART_GEOMETRY = Object.freeze({ width: 276, height: 142, left: 36, right: 7, top: 18, bottom: 36 });

function renderFluenceDensity(revealedOnly = false) {
  if (!blastResults) return;
  const svg = document.getElementById("fluenceDensityChart"), { width, height, left, right, top, bottom } = DENSITY_CHART_GEOMETRY, margin = { left, right, top, bottom }, innerWidth = width - left - right, innerHeight = height - top - bottom;
  const model = countDistributionModel(blastResults, revealedOnly), maximumCount = Math.max(1, ...model.samples.map(sample => sample.count));
  const [domainMin, domainMax] = blastResults.fluenceDomain, logMin = Math.log10(domainMin), logMax = Math.log10(domainMax), xFor = value => margin.left + THREE.MathUtils.clamp((Math.log10(value) - logMin) / (logMax - logMin), 0, 1) * innerWidth;
  const curvePoints = model.samples.map(sample => `${(margin.left + (sample.x - logMin) / (logMax - logMin) * innerWidth).toFixed(2)},${(margin.top + innerHeight - sample.count / maximumCount * innerHeight).toFixed(2)}`), curvePath = `M${curvePoints.join(" L")}`, areaPath = `${curvePath} L${width - margin.right},${margin.top + innerHeight} L${margin.left},${margin.top + innerHeight} Z`;
  const selectedX = xFor(selectedAnalysisThreshold), referenceX = xFor(PERMANENT_DAMAGE_THRESHOLD_J_M2);
  const gradientValues = [domainMin, ...FLUENCE_COLOR_STOPS.map(stop => stop.value).filter(value => value > domainMin && value < domainMax), domainMax];
  const gradientStops = gradientValues.map(value => `<stop offset="${normalizedLogFluence(value, blastResults.fluenceDomain).toFixed(6)}" stop-color="${fluenceColor(value)}"/>`).join("");
  const selectedLabel = formatFluence(selectedAnalysisThreshold), selectedLabelWidth = Math.max(17, selectedLabel.length * 4.5 + 6), selectedLabelX = THREE.MathUtils.clamp(selectedX - selectedLabelWidth / 2, margin.left - 3, width - margin.right - selectedLabelWidth + 3);
  const selectedLine = `<g id="thresholdDragControl" class="histogramThresholdControl" tabindex="0" role="slider" aria-label="Selected analysis threshold" aria-valuemin="${domainMin}" aria-valuemax="${domainMax}" aria-valuenow="${selectedAnalysisThreshold}" aria-valuetext="${selectedLabel} joules per square metre"><line class="histogramThresholdHit" x1="${selectedX}" y1="${margin.top - 5}" x2="${selectedX}" y2="${margin.top + innerHeight + 5}"/><line class="histogramSelectedThreshold" x1="${selectedX}" y1="${margin.top}" x2="${selectedX}" y2="${margin.top + innerHeight}"/><rect class="selectedThresholdLabelBackground" x="${selectedLabelX}" y="${height - 28.5}" width="${selectedLabelWidth}" height="11" rx="3"/><text class="histogramTick selectedTick" x="${selectedLabelX + selectedLabelWidth / 2}" y="${height - 21}" text-anchor="middle">${selectedLabel}</text></g>`;
  svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
  const referenceLabelAnchor = referenceX > width - 48 ? "end" : "start", referenceLabelX = referenceX + (referenceLabelAnchor === "start" ? 3 : -3), yMaximumLabel = Math.ceil(maximumCount).toLocaleString();
  svg.innerHTML = `<defs><linearGradient id="distributionFill" gradientUnits="userSpaceOnUse" x1="${margin.left}" x2="${width - margin.right}">${gradientStops}</linearGradient></defs><path class="densityArea" d="${areaPath}"/><path class="densityCurve" d="${curvePath}"/><line class="histogramAxis" x1="${margin.left}" y1="${margin.top + innerHeight}" x2="${width - margin.right}" y2="${margin.top + innerHeight}"/><line class="histogramThreshold" style="stroke:${fluenceColor(PERMANENT_DAMAGE_THRESHOLD_J_M2)}" x1="${referenceX}" y1="${margin.top}" x2="${referenceX}" y2="${margin.top + innerHeight}"/><text class="referenceThresholdLabel" x="${referenceLabelX}" y="${margin.top + 8}" text-anchor="${referenceLabelAnchor}">40 J/m²</text><text class="histogramTick" x="${margin.left}" y="${height - 21}" text-anchor="start">${formatFluence(domainMin)}</text><text class="histogramTick" x="${width - margin.right}" y="${height - 21}" text-anchor="end">${formatFluence(domainMax)}</text>${selectedLine}<text class="chartAxisTitle" x="${margin.left + innerWidth / 2}" y="${height - 6}" text-anchor="middle">Prompt X-ray fluence (J/m²)</text><text class="histogramTick" x="${margin.left - 5}" y="${margin.top + 4}" text-anchor="end">${yMaximumLabel}</text><text class="histogramTick" x="${margin.left - 5}" y="${margin.top + innerHeight}" text-anchor="end">0</text><text class="chartAxisTitle" transform="translate(9 ${margin.top + innerHeight / 2}) rotate(-90)" text-anchor="middle">Satellites exposed</text><title>Smoothed satellite count frequency across prompt X-ray fluence.</title>`;
}

function cancelThresholdNudge() { thresholdNudgeShown = true; thresholdNudgeAnimation?.control?.removeAttribute("transform"); thresholdNudgeAnimation = null; document.getElementById("thresholdDragControl")?.classList.remove("thresholdNudge"); if (window.__thresholdNudgeAudit) window.__thresholdNudgeAudit.cancelled = true; }
function startThresholdNudge() {
  if (thresholdNudgeShown) return;
  thresholdNudgeShown = true;
  const reducedMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;
  window.__thresholdNudgeAudit = { started: !reducedMotion, reducedMotion, completed: false, cancelled: false };
  if (reducedMotion) return;
  const control = document.getElementById("thresholdDragControl");
  if (!control) return;
  thresholdNudgeAnimation = { control, startedAt: performance.now(), duration: 1350 };
}
function updateThresholdNudge(now) {
  if (!thresholdNudgeAnimation) return;
  const { control, startedAt, duration } = thresholdNudgeAnimation, progress = Math.min(1, (now - startedAt) / duration);
  const offset = progress < .25 ? 9 * progress / .25 : progress < .52 ? 9 - 14 * (progress - .25) / .27 : progress < .75 ? -5 + 7 * (progress - .52) / .23 : 2 - 2 * (progress - .75) / .25;
  control.setAttribute("transform", `translate(${offset.toFixed(3)} 0)`);
  if (progress === 1) { control.removeAttribute("transform"); window.__thresholdNudgeAudit.completed = true; thresholdNudgeAnimation = null; }
}

function ownerDisplayName(code) {
  if (code === "CIS") return "Russia";
  if (code === "PRC") return "China";
  return ownerCodeMetadata?.mapping?.[code] || `Unknown (${code})`;
}

function cardinalCoordinate(value, positive, negative) {
  return `${Math.abs(value).toFixed(1)}° ${value >= 0 ? positive : negative}`;
}

function tooltipRow(term, description, className = "") {
  const dt = document.createElement("dt"), dd = document.createElement("dd"); dt.textContent = term; dd.textContent = description; if (className) dd.className = className; return [dt, dd];
}

function showSatelliteTooltip(index, clientX, clientY) {
  const row = catalog[index], tooltip = document.getElementById("satelliteTooltip"); if (!row) { tooltip.hidden = true; return; }
  const metadata = analyticalMetadataFor(row.NORAD_CAT_ID), result = blastResults?.records[index], position = new THREE.Vector3().fromBufferAttribute(points.geometry.attributes.position, index), geodetic = scenePositionToGeodetic(position), title = document.createElement("strong"), details = document.createElement("dl");
  title.textContent = row.OBJECT_NAME || "Unnamed payload";
  const rows = [
    ["NORAD ID", String(row.NORAD_CAT_ID)], ["COSPAR ID", row.OBJECT_ID || "Unavailable"], ["Country / Owner", ownerDisplayName(row.OWNER)], ["Catalog status", "Active payload"], ["Mission", metadata.missionPurpose || row.MISSION_CLASS || "Unknown"], ["Constellation", metadata.constellation || "Other"], ["Altitude", `${geodetic.altitudeKm.toLocaleString()} km`], ["Latitude", cardinalCoordinate(geodetic.latitudeDegrees, "N", "S")], ["Longitude", cardinalCoordinate(geodetic.longitudeDegrees, "E", "W")], ["Element epoch", row.EPOCH]
  ];
  if (result) {
    const above = !result.earthMasked && result.fluenceJm2 >= selectedAnalysisThreshold, mappedColor = result.earthMasked ? INTERFACE_DARK_TEXT : fluenceColor(result.fluenceJm2), readableColor = above ? statisticNumberColor(mappedColor) : "#777777";
    rows.push(["Prompt exposure", result.earthMasked ? "Blocked by solid Earth" : `${formatFluence(result.fluenceJm2)} J/m²`, `promptExposure ${above ? "aboveThreshold" : "belowThreshold"}`]);
    tooltip.style.setProperty("--tooltip-exposure-color", readableColor);
  } else tooltip.style.removeProperty("--tooltip-exposure-color");
  rows.forEach(([term, description, className]) => details.append(...tooltipRow(term, description, className))); tooltip.replaceChildren(title, details); tooltip.hidden = false;
  const width = tooltip.offsetWidth, height = tooltip.offsetHeight; tooltip.style.left = `${Math.min(innerWidth - width - 10, clientX + 14)}px`; tooltip.style.top = `${Math.min(innerHeight - height - 10, Math.max(10, clientY + 14))}px`;
  window.__satelliteTooltipAudit = { catalogIndex: index, catalogId: String(row.NORAD_CAT_ID), fields: rows.map(([term]) => term), noClickAction: true };
}

function updateSatelliteHover() {
  satelliteHoverFrame = null; const event = latestSatelliteHoverEvent, tooltip = document.getElementById("satelliteTooltip");
  if (!event || !points || !points.visible) { tooltip.hidden = true; return; }
  const rect = renderer.domElement.getBoundingClientRect(); payloadPointer.set((event.clientX - rect.left) / rect.width * 2 - 1, -(event.clientY - rect.top) / rect.height * 2 + 1); payloadRaycaster.params.Points.threshold = Math.max(.012, camera.position.distanceTo(controls.target) * .0045); payloadRaycaster.setFromCamera(payloadPointer, camera);
  const alphas = points.geometry.attributes.effectAlpha.array, positions = points.geometry.attributes.position, intersections = payloadRaycaster.intersectObject(points, false); let selected = null;
  for (const intersection of intersections) { const index = intersection.index, position = new THREE.Vector3().fromBufferAttribute(positions, index); if (alphas[index] <= .025 || segmentIntersectsSphere(camera.position.toArray(), position.toArray(), .999)) continue; selected = index; break; }
  if (selected === null) tooltip.hidden = true; else showSatelliteTooltip(selected, event.clientX, event.clientY);
}

renderer.domElement.addEventListener("pointermove", event => { latestSatelliteHoverEvent = { clientX: event.clientX, clientY: event.clientY }; if (satelliteHoverFrame === null) satelliteHoverFrame = requestAnimationFrame(updateSatelliteHover); });
renderer.domElement.addEventListener("pointerleave", () => { latestSatelliteHoverEvent = null; document.getElementById("satelliteTooltip").hidden = true; });

function groupedAffectedStats(records, accessor, order) {
  const groups = new Map(order.map(label => [label, []]));
  records.forEach(record => { const label = accessor(record); if (!groups.has(label)) groups.set(label, []); groups.get(label).push(record.fluenceJm2); });
  return order.map(label => {
    const values = groups.get(label) || [], sorted = [...values].sort((a, b) => a - b), middle = Math.floor(sorted.length / 2), median = sorted.length ? (sorted.length % 2 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2) : 0;
    return { label, count: values.length, proportion: records.length ? values.length / records.length : 0, medianFluence: median };
  });
}

function analysisButton(stat, dimension, states, detail = null) {
  const state = categoryState(states, stat.label), nextState = state === CATEGORY_STATES.NEUTRAL ? CATEGORY_STATES.FOCUS : state === CATEGORY_STATES.FOCUS ? CATEGORY_STATES.EXCLUDE : CATEGORY_STATES.NEUTRAL;
  const button = document.createElement("button"), label = document.createElement("span"), value = document.createElement("span"), stateIndicator = document.createElement("span");
  button.type = "button"; button.className = "analysisBreakdownButton analysisBarRow"; button.dataset.dimension = dimension; button.dataset.key = stat.label; button.dataset.state = state; button.setAttribute("aria-pressed", state === CATEGORY_STATES.FOCUS ? "true" : "false"); button.setAttribute("aria-label", `${stat.label}: ${stat.count.toLocaleString()} exposed satellites, ${(stat.proportion * 100).toFixed(1)} percent. Current state ${state}. Activate for ${nextState}.`); button.style.setProperty("--bar-width", `${stat.count ? Math.max(1.5, stat.proportion * 100) : 0}%`); button.disabled = appState !== APP_STATES.RESULTS;
  label.className = "analysisLabel"; value.className = "analysisValue"; stateIndicator.className = "analysisState"; label.textContent = stat.label; value.textContent = detail || `${stat.count.toLocaleString()} · ${(stat.proportion * 100).toFixed(1)}%`; stateIndicator.textContent = state === CATEGORY_STATES.FOCUS ? "●" : state === CATEGORY_STATES.EXCLUDE ? "×" : ""; stateIndicator.setAttribute("aria-hidden", "true");
  button.append(label, value, stateIndicator); return button;
}

function renderBreakdown(containerId, summaryId, records, accessor, order, states, dimension, detailFor = null) {
  const container = document.getElementById(containerId), stats = groupedAffectedStats(records, accessor, order); container.replaceChildren();
  stats.sort((a, b) => b.count - a.count || order.indexOf(a.label) - order.indexOf(b.label)).forEach(stat => {
    const detail = detailFor ? detailFor(stat) : null;
    container.appendChild(analysisButton(stat, dimension, states, detail));
  });
  document.getElementById(summaryId).textContent = `${records.length.toLocaleString()} in scope`;
}

function updateAffectedDashboard(baseRecords = thresholdPopulation()) {
  const countryRecords = baseRecords.filter(record => recordMatchesDrilldowns(record, "country"));
  const missionRecords = baseRecords.filter(record => recordMatchesDrilldowns(record, "mission"));
  const constellationRecords = baseRecords.filter(record => recordMatchesDrilldowns(record, "constellation"));
  renderBreakdown("countryBreakdown", "countryBreakdownSummary", countryRecords, countryGroup, COUNTRY_GROUPS, selectedCountryDrilldowns, "country");
  renderBreakdown("missionBreakdown", "missionBreakdownSummary", missionRecords, record => record.missionPurpose, MISSION_PURPOSES, selectedMissionDrilldowns, "mission");
  renderBreakdown("constellationBreakdown", "constellationBreakdownSummary", constellationRecords, record => record.constellation, CONSTELLATION_GROUPS, selectedConstellationDrilldowns, "constellation", stat => { const total = analysisMetadata?.constellation_counts?.[stat.label] || 0; return `${stat.count.toLocaleString()} / ${total.toLocaleString()}`; });
  const filteredRecords = baseRecords.filter(recordMatchesDrilldowns);
  document.getElementById("clearDrilldownsBtn").disabled = appState !== APP_STATES.RESULTS || !hasActiveDrilldown();
  window.__affectedDashboardAudit = { aboveThresholdCount: baseRecords.length, filteredCount: filteredRecords.length, countryCountTotal: groupedAffectedStats(countryRecords, countryGroup, COUNTRY_GROUPS).reduce((sum, stat) => sum + stat.count, 0), missionCountTotal: groupedAffectedStats(missionRecords, record => record.missionPurpose, MISSION_PURPOSES).reduce((sum, stat) => sum + stat.count, 0), constellationCountTotal: groupedAffectedStats(constellationRecords, record => record.constellation, CONSTELLATION_GROUPS).reduce((sum, stat) => sum + stat.count, 0), commonRowComponent: true };
}

function selectedDrilldownSet(dimension) { return dimension === "country" ? selectedCountryDrilldowns : dimension === "mission" ? selectedMissionDrilldowns : selectedConstellationDrilldowns; }
function clearDrilldowns() { selectedCountryDrilldowns.clear(); selectedMissionDrilldowns.clear(); selectedConstellationDrilldowns.clear(); updateAnalysisStats(); applyResultStyling(); }

function updateTimingBattle(sample, fleetA, fleetB) {
  const battle = document.getElementById("timingBattle"), total = sample.fleetACount + sample.fleetBCount, shareA = total ? sample.fleetACount / total * 100 : 50;
  battle.hidden = false; document.getElementById("timingBattleFleetA").textContent = `${fleetA} · ${sample.fleetACount.toLocaleString()}`; document.getElementById("timingBattleFleetB").textContent = `${fleetB} · ${sample.fleetBCount.toLocaleString()}`;
  document.getElementById("timingBattleA").style.width = `${shareA}%`; document.getElementById("timingBattleB").style.width = `${100 - shareA}%`;
}

function timingObjectiveScore(sample) { return sample.fleetACount - sample.fleetBCount; }

function renderTimingAnalysis(best, baseline, fleetA, fleetB, threshold) {
  const summary = document.getElementById("timingAnalysisSummary"), timingPhrase = best.offsetSeconds < -1 ? `${Math.round(Math.abs(best.offsetSeconds) / 60)} minutes earlier` : best.offsetSeconds > 1 ? `${Math.round(best.offsetSeconds / 60)} minutes later` : "at the selected time", improvement = timingObjectiveScore(best) - timingObjectiveScore(baseline), unit = Math.abs(improvement) === 1 ? "satellite" : "satellites", fleetANoun = best.fleetACount === 1 ? "satellite" : "satellites", fleetBNoun = best.fleetBCount === 1 ? "satellite" : "satellites", improvementSentence = improvement > 0 ? `Timing selection improves the exposure difference in favor of <b>${fleetA}</b> over <b>${fleetB}</b> by <strong>${improvement.toLocaleString()} ${unit}</strong> compared with detonating at the originally selected time.` : `The sampled timing produces no improvement in the exposure difference between <b>${fleetA}</b> and <b>${fleetB}</b> over the originally selected time.`;
  updateTimingBattle(best, fleetA, fleetB);
  summary.hidden = false; summary.innerHTML = `<p>If the weapon were detonated <strong>${timingPhrase}</strong>, <b>${best.fleetACount.toLocaleString()} ${fleetA}</b> ${fleetANoun} and <b>${best.fleetBCount.toLocaleString()} ${fleetB}</b> ${fleetBNoun} would be exposed to more than ${formatFluence(threshold)} J/m². ${improvementSentence}</p>`;
  requestAnimationFrame(() => { summary.scrollIntoView({ behavior: "smooth", block: "nearest" }); window.__timingSummaryScrollAudit = { requested: true, fleetA, fleetB }; });
}

function timingSelectionLabel(select) { return select.options[select.selectedIndex].textContent; }
function timingSelectionIncludes(index, selection) {
  const [dimension, label] = selection.split(":");
  return dimension === "country" ? countryGroup({ ownerCode: catalog[index].OWNER }) === label : analyticalMetadataFor(catalog[index].NORAD_CAT_ID).constellation === label;
}
function timingCarrierVisualPosition(seconds, trajectoryRotation) {
  return carrierPlanePoint(carrierTrueAnomalyAt(seconds), false).applyAxisAngle(EARTH_NORTH, trajectoryRotation);
}
function timingCarrierView(point, snapshot = null, blend = 1) {
  const desiredPosition = point.clone().normalize().multiplyScalar(4.1), desiredTarget = new THREE.Vector3();
  if (snapshot && blend < 1) { camera.position.lerpVectors(snapshot.position, desiredPosition, blend); controls.target.lerpVectors(snapshot.target, desiredTarget, blend); }
  else { camera.position.copy(desiredPosition); controls.target.copy(desiredTarget); }
  camera.up.copy(geographicNorthUp(camera.position, controls.target, snapshot?.up || camera.up)); camera.lookAt(controls.target); controls.update();
}
function animateTimingCarrierStep(fromSeconds, toSeconds, trajectoryRotation, runId, duration = 130, cameraBlendSnapshot = null) {
  return new Promise(resolve => { const startedAt = performance.now(); function frame(now) { if (runId !== timingAnalysisRunId || appState !== APP_STATES.RESULTS) { resolve(); return; } const progress = Math.min(1, (now - startedAt) / duration), eased = progress * progress * (3 - 2 * progress), seconds = THREE.MathUtils.lerp(fromSeconds, toSeconds, eased), point = timingCarrierVisualPosition(seconds, trajectoryRotation); carrierSprite.position.copy(point); timingCarrierView(point, cameraBlendSnapshot, cameraBlendSnapshot ? eased : 1); const audit = window.__timingCarrierTourAudit; if (audit) { audit.frameCount++; if (audit.frameCount % 5 === 0) { audit.carrierPositions.push(point.toArray()); audit.cameraPositions.push(camera.position.toArray()); } } if (progress < 1) requestAnimationFrame(frame); else resolve(); } requestAnimationFrame(frame); });
}

async function runAlternateTimingAnalysis() {
  if (appState !== APP_STATES.RESULTS || !blastResults) return;
  const fleetASelect = document.getElementById("timingFleetA"), fleetBSelect = document.getElementById("timingFleetB"), fleetASelection = fleetASelect.value, fleetBSelection = fleetBSelect.value, fleetA = timingSelectionLabel(fleetASelect), fleetB = timingSelectionLabel(fleetBSelect), button = document.getElementById("timingAnalyzeBtn"), status = document.getElementById("timingAnalysisStatus");
  if (fleetASelection === fleetBSelection) { status.textContent = "Choose two different fleets or countries."; status.hidden = false; return; }
  const runId = ++timingAnalysisRunId, threshold = selectedAnalysisThreshold, yieldKt = blastResults.yieldKt, centerSeconds = resultDetonationSimulationSeconds, periodSeconds = Math.PI * 2 * Math.sqrt(Math.pow(carrierOrbit.semiMajor, 3) / MU_EARTH_KM3_S2), sampleCount = 41;
  const fleetAIndices = [], fleetBIndices = [];
  catalog.forEach((row, index) => { if (timingSelectionIncludes(index, fleetASelection)) fleetAIndices.push(index); if (timingSelectionIncludes(index, fleetBSelection)) fleetBIndices.push(index); });
  const tourSnapshot = { position: camera.position.clone(), target: controls.target.clone(), up: camera.up.clone(), carrierPosition: carrierSprite.position.clone(), controlsEnabled: controls.enabled, trajectoryRotation: trajectoryGroup.rotation.y };
  button.disabled = true; ["timingFleetA", "timingFleetB"].forEach(id => { document.getElementById(id).disabled = true; }); document.getElementById("timingAnalysisSummary").hidden = true; document.getElementById("timingBattle").hidden = false; status.textContent = ""; status.hidden = true; controls.enabled = false; cameraTransition = null;
  const samples = [], firstSeconds = centerSeconds - periodSeconds / 2;
  window.__timingCarrierTourAudit = { frameCount: 0, carrierPositions: [], cameraPositions: [], usesRenderedTrajectoryRotation: true, restored: false };
  try {
    await animateTimingCarrierStep(centerSeconds, firstSeconds, tourSnapshot.trajectoryRotation, runId, 900, tourSnapshot);
    for (let sampleIndex = 0; sampleIndex < sampleCount; sampleIndex++) {
      if (runId !== timingAnalysisRunId || appState !== APP_STATES.RESULTS) return;
      const offsetSeconds = -periodSeconds / 2 + sampleIndex / (sampleCount - 1) * periodSeconds, candidateSeconds = centerSeconds + offsetSeconds, epoch = new Date(catalogEpoch.getTime() + candidateSeconds * 1000), burstScene = carrierPosition(candidateSeconds), gmst = satellite.gstime(epoch), burstEci = satellite.ecfToEci(sceneToEcfKm(burstScene), gmst);
      const resultPromise = requestPromptCalculation({ epoch: epoch.toISOString(), burstEciKm: [burstEci.x, burstEci.y, burstEci.z], yieldKt, earthRadiusKm: EARTH_RADIUS_KM });
      const previousSeconds = sampleIndex ? centerSeconds - periodSeconds / 2 + (sampleIndex - 1) / (sampleCount - 1) * periodSeconds : firstSeconds;
      const [result] = await Promise.all([resultPromise, animateTimingCarrierStep(previousSeconds, candidateSeconds, tourSnapshot.trajectoryRotation, runId)]);
      const affected = index => result.propagationValid[index] && !result.earthMasked[index] && result.fluenceJm2[index] >= threshold;
      const sample = { offsetSeconds, epoch: epoch.toISOString(), fleetACount: fleetAIndices.reduce((count, index) => count + Number(affected(index)), 0), fleetBCount: fleetBIndices.reduce((count, index) => count + Number(affected(index)), 0) }; samples.push(sample); updateTimingBattle(sample, fleetA, fleetB);
    }
    const best = samples.reduce((winner, sample) => timingObjectiveScore(sample) > timingObjectiveScore(winner) ? sample : winner, samples[0]), baseline = samples.reduce((nearest, sample) => Math.abs(sample.offsetSeconds) < Math.abs(nearest.offsetSeconds) ? sample : nearest, samples[0]);
    timingAnalysisResult = { fleetA, fleetB, threshold, yieldKt, carrierPeriodSeconds: periodSeconds, samples, best, baseline }; renderTimingAnalysis(best, baseline, fleetA, fleetB, threshold);
    window.__alternateTimingAudit = { metric: "satellites-above-selected-threshold", objective: "maximize-fleet-a-minus-fleet-b", cumulativeFluenceUsed: false, sampleCount, thresholdJm2: threshold, fleetASelection, fleetBSelection, fleetA, fleetB, best, baseline, improvement: timingObjectiveScore(best) - timingObjectiveScore(baseline), tracedRenderedCarrierOrbit: true, returnedToStartingView: true };
  } catch (error) { console.error(error); status.textContent = `Timing analysis failed: ${error.message}`; status.hidden = false; }
  finally { carrierSprite.position.copy(tourSnapshot.carrierPosition); camera.position.copy(tourSnapshot.position); controls.target.copy(tourSnapshot.target); camera.up.copy(tourSnapshot.up); camera.lookAt(controls.target); controls.enabled = tourSnapshot.controlsEnabled; controls.update(); if (window.__timingCarrierTourAudit) { window.__timingCarrierTourAudit.carrierRestorationError = carrierSprite.position.distanceTo(tourSnapshot.carrierPosition); window.__timingCarrierTourAudit.cameraRestorationError = camera.position.distanceTo(tourSnapshot.position); window.__timingCarrierTourAudit.restored = true; } if (runId === timingAnalysisRunId && appState === APP_STATES.RESULTS) { button.disabled = false; ["timingFleetA", "timingFleetB"].forEach(id => { document.getElementById(id).disabled = false; }); } }
}

document.getElementById("timingAnalyzeBtn").addEventListener("click", runAlternateTimingAnalysis);
document.getElementById("resultsDisclosureBtn").addEventListener("click", event => {
  if (appState !== APP_STATES.RESULTS) return;
  const details = document.getElementById("resultsDetails"), expanded = event.currentTarget.getAttribute("aria-expanded") === "true";
  event.currentTarget.setAttribute("aria-expanded", String(!expanded)); details.hidden = expanded; applyResultStyling();
});

function updateAnalysisStats() {
  if (!blastResults) return;
  const selected = thresholdPopulation(), displayedAffected = selected.filter(recordMatchesDrilldowns);
  const thresholdLabel = `${formatFluence(selectedAnalysisThreshold)} J/m²`, thresholdScaleColor = fluenceColor(selectedAnalysisThreshold), numberColor = statisticNumberColor(thresholdScaleColor), primaryResult = document.querySelector(".primaryResult");
  primaryResult.style.setProperty("--fluence-accent", thresholdScaleColor); primaryResult.style.setProperty("--stat-number-color", numberColor);
  document.getElementById("aboveThresholdCount").textContent = displayedAffected.length.toLocaleString();
  window.__headlineThresholdColorAudit = { thresholdJm2: selectedAnalysisThreshold, scaleColor: thresholdScaleColor, statisticAccent: thresholdScaleColor, statisticNumberColor: numberColor, cardBackground: STATISTIC_CARD_BACKGROUND, contrastRatio: contrastRatio(thresholdScaleColor, STATISTIC_CARD_BACKGROUND), usedDarkTextFallback: numberColor === INTERFACE_DARK_TEXT };
  document.getElementById("selectedThresholdParameter").textContent = thresholdLabel;
  updateAffectedDashboard(selected);
}

function formatYieldLabel(yieldKt) { return yieldKt >= 1000 ? `${yieldKt / 1000} Mt` : `${yieldKt.toLocaleString()} kt`; }
function formatDetonationTime(isoDate) { return new Intl.DateTimeFormat("en-US", { month: "short", day: "numeric", year: "numeric", hour: "2-digit", minute: "2-digit", hour12: false, timeZone: "UTC", timeZoneName: "short" }).format(new Date(isoDate)); }

function updateScenarioMetadata() {
  if (!blastResults) return;
  const geodetic = scenePositionToGeodetic(blastResults.burstScene);
  document.getElementById("resultsDescription").textContent = `Modeled X-ray fluence for a ${formatYieldLabel(blastResults.yieldKt)}-yield detonation at ${cardinalCoordinate(geodetic.latitudeDegrees, "N", "S")}, ${cardinalCoordinate(geodetic.longitudeDegrees, "E", "W")}, ${geodetic.altitudeKm.toFixed(1)} km altitude, on ${formatDetonationTime(blastResults.detonationEpoch)}.`;
  document.getElementById("methodologyCitations").innerHTML = `<p><span class="citation">Fang and Igor Morić, “Assessing the Impact of the Prompt Effect of a High-Altitude Nuclear Explosion on Non-Military LEO Satellites,” <cite>Science &amp; Global Security</cite> (forthcoming).</span> <span class="citationNote">Used for the prompt X-ray fluence relationship, yield cases, Earth masking, and 40 J/m² reference threshold.</span></p><p><span class="citation">T. S. Kelso, “Current GP Element Sets” and “Satellite Catalog,” <cite>CelesTrak</cite>, <a href="https://celestrak.org/" target="_blank" rel="noreferrer">celestrak.org</a>.</span> <span class="citationNote">Used for active-payload orbital elements and object-type filtering.</span></p><p><span class="citation">Jonathan C. McDowell, <cite>General Catalog of Artificial Space Objects</cite>, release 1.8.8 (2026), <a href="https://planet4589.org/space/gcat/" target="_blank" rel="noreferrer">planet4589.org/space/gcat</a>.</span> <span class="citationNote">Used for mission-purpose and constellation/program classifications joined by exact COSPAR identifier.</span></p><p><span class="citation">David A. Vallado, Paul Crawford, Richard Hujsak, and T. S. Kelso, “Revisiting Spacetrack Report #3,” paper presented at the AIAA/AAS Astrodynamics Specialist Conference, Keystone, CO, August 21–24, 2006.</span> <span class="citationNote">Used as the SGP4 propagation reference for detonation analytics.</span></p>`;
  document.getElementById("copyShareLinkBtn").dataset.shareUrl = buildShareUrl();
}

function applyResultStyling() {
  if (!blastResults || !points) return;
  const colors = points.geometry.attributes.effectColor.array, scales = points.geometry.attributes.effectScale.array, alphas = points.geometry.attributes.effectAlpha.array;
  const drilling = hasActiveDrilldown(), thresholdFocus = document.getElementById("resultsDisclosureBtn").getAttribute("aria-expanded") === "true", focusedResults = drilling || thresholdFocus; let enlargedCount = 0, visibleCount = 0, displayedAffectedCount = 0;
  blastResults.records.forEach(record => {
    const index = renderIndexByCatalogId.get(record.catalogId); if (index === undefined) return;
    const includedByFilters = recordMatchesDrilldowns(record), affected = record.propagationValid && !record.earthMasked && record.fluenceJm2 >= selectedAnalysisThreshold, displayedAffected = affected && includedByFilters, enlarged = drilling ? displayedAffected : affected;
    if (!focusedResults) alphas[index] = record.earthMasked ? .34 : .98;
    else if (displayedAffected) alphas[index] = .98;
    else if (drilling && !includedByFilters) alphas[index] = 0;
    else alphas[index] = record.earthMasked ? .06 : .10;
    scales[index] = enlarged ? 1.72 : 1;
    if (alphas[index] > .1) visibleCount++; if (enlarged) enlargedCount++; if (displayedAffected) displayedAffectedCount++;
  });
  points.geometry.attributes.effectScale.needsUpdate = points.geometry.attributes.effectAlpha.needsUpdate = true;
  let colorChecksum = 0, opacityChecksum = 0;
  for (let index = 0; index < alphas.length; index++) { const weight = index % 97 + 1; opacityChecksum += alphas[index] * weight; colorChecksum += (colors[index * 3] * 3 + colors[index * 3 + 1] * 5 + colors[index * 3 + 2] * 7) * weight; }
  window.__promptEffectsVisualAudit = { thresholdJm2: selectedAnalysisThreshold, thresholdFocus, affectedCount: thresholdPopulation().length, displayedAffectedCount, enlargedCount, visibleCount, colorChecksum, opacityChecksum, storedFluenceUnchangedByFilters: true };
}

function updateThreshold(value) {
  if (!blastResults || !Number.isFinite(value)) return;
  selectedAnalysisThreshold = THREE.MathUtils.clamp(value, blastResults.fluenceDomain[0], blastResults.fluenceDomain[1]);
  if (timingAnalysisResult && Math.abs(timingAnalysisResult.threshold - selectedAnalysisThreshold) > 1e-9) { const status = document.getElementById("timingAnalysisStatus"); status.textContent = "Selected threshold changed; rerun the timing analysis to update its counts."; status.hidden = false; }
  renderFluenceDensity(appState === APP_STATES.DETONATION); updateAnalysisStats(); updateScenarioMetadata();
  if (appState === APP_STATES.RESULTS) applyResultStyling();
}

function showFluenceResults() {
  const result = blastResults, panel = document.getElementById("fluenceResults"); if (!result) return;
  panel.hidden = false;
  selectedAnalysisThreshold = THREE.MathUtils.clamp(selectedAnalysisThreshold, result.fluenceDomain[0], result.fluenceDomain[1]);
  document.getElementById("resultsDisclosureBtn").setAttribute("aria-expanded", "false"); document.getElementById("resultsDetails").hidden = true;
  updateThreshold(selectedAnalysisThreshold); renderFluenceDensity(true);
}

function buildShareUrl() {
  if (!blastResults) return location.href;
  const params = new URLSearchParams({ scenario: "v1", snapshot: catalogMetadata.snapshot, epoch: blastResults.detonationEpoch, yield: String(blastResults.yieldKt), threshold: String(selectedAnalysisThreshold), a: String(carrierOrbit.semiMajor), e: String(carrierOrbit.eccentricity), i: String(carrierOrbit.inclination), raan: String(carrierOrbit.raan), argp: String(carrierOrbit.argPerigee), m0: String(carrierOrbit.epochAnomaly) });
  if (carrierBaseCatalogId) params.set("carrier", carrierBaseCatalogId);
  return `${location.origin}${location.pathname}?${params}`;
}

async function copyText(text) {
  try { await navigator.clipboard.writeText(text); return true; }
  catch (error) { const fallback = document.createElement("textarea"); fallback.value = text; fallback.style.position = "fixed"; fallback.style.opacity = "0"; document.body.appendChild(fallback); fallback.select(); const copied = document.execCommand("copy"); fallback.remove(); return copied; }
}

function thresholdFromClientX(clientX) {
  const svg = document.getElementById("fluenceDensityChart"), rect = svg.getBoundingClientRect(), { width, left, right } = DENSITY_CHART_GEOMETRY;
  const svgX = (clientX - rect.left) / Math.max(1, rect.width) * width, fraction = THREE.MathUtils.clamp((svgX - left) / (width - left - right), 0, 1);
  const [minimum, maximum] = blastResults.fluenceDomain, rawValue = 10 ** (Math.log10(minimum) + fraction * (Math.log10(maximum) - Math.log10(minimum))), referenceFraction = (Math.log10(PERMANENT_DAMAGE_THRESHOLD_J_M2) - Math.log10(minimum)) / (Math.log10(maximum) - Math.log10(minimum)), referenceX = left + referenceFraction * (width - left - right);
  return Math.abs(svgX - referenceX) <= 10 ? PERMANENT_DAMAGE_THRESHOLD_J_M2 : rawValue;
}
let thresholdDragging = false;
function cancelThresholdSlide() { if (thresholdSlideAnimation) thresholdSlideAnimation.cancelled = true; thresholdSlideAnimation = null; }
function animateThresholdTo(targetValue) {
  cancelThresholdSlide();
  const animation = { cancelled: false, startedAt: performance.now(), duration: 460, fromLog: Math.log10(selectedAnalysisThreshold), toLog: Math.log10(targetValue) }; thresholdSlideAnimation = animation;
  window.__thresholdSlideAudit = { from: selectedAnalysisThreshold, to: targetValue, completed: false };
  function frame(now) {
    if (animation.cancelled || !thresholdIsInteractive()) return;
    const progress = Math.min(1, (now - animation.startedAt) / animation.duration), eased = 1 - Math.pow(1 - progress, 3);
    updateThreshold(progress === 1 ? targetValue : 10 ** THREE.MathUtils.lerp(animation.fromLog, animation.toLog, eased));
    if (progress < 1) requestAnimationFrame(frame); else { thresholdSlideAnimation = null; window.__thresholdSlideAudit.completed = true; }
  }
  requestAnimationFrame(frame);
}
document.getElementById("fluenceDensityChart").addEventListener("pointerdown", event => {
  cancelThresholdNudge(); if (!thresholdIsInteractive()) return;
  event.currentTarget.setPointerCapture?.(event.pointerId);
  if (event.target.closest(".histogramThresholdControl")) { cancelThresholdSlide(); thresholdDragging = true; event.preventDefault(); updateThreshold(thresholdFromClientX(event.clientX)); return; }
  const rect = event.currentTarget.getBoundingClientRect(), svgY = (event.clientY - rect.top) / Math.max(1, rect.height) * DENSITY_CHART_GEOMETRY.height;
  if (svgY >= DENSITY_CHART_GEOMETRY.top && svgY <= DENSITY_CHART_GEOMETRY.height - DENSITY_CHART_GEOMETRY.bottom) { event.preventDefault(); animateThresholdTo(thresholdFromClientX(event.clientX)); }
});
addEventListener("pointermove", event => { if (thresholdDragging) updateThreshold(thresholdFromClientX(event.clientX)); });
addEventListener("pointerup", event => { if (!thresholdDragging) return; thresholdDragging = false; updateThreshold(thresholdFromClientX(event.clientX)); });
document.getElementById("fluenceDensityChart").addEventListener("keydown", event => {
  cancelThresholdNudge(); cancelThresholdSlide();
  if (!thresholdIsInteractive() || event.target.id !== "thresholdDragControl") return;
  const [minimum, maximum] = blastResults.fluenceDomain, factor = 10 ** (event.shiftKey ? .1 : .025); let value = selectedAnalysisThreshold;
  if (event.key === "ArrowLeft" || event.key === "ArrowDown") value /= factor;
  else if (event.key === "ArrowRight" || event.key === "ArrowUp") value *= factor;
  else if (event.key === "Home") value = minimum;
  else if (event.key === "End") value = maximum;
  else return;
  event.preventDefault(); updateThreshold(value); requestAnimationFrame(() => document.getElementById("thresholdDragControl")?.focus());
});
document.getElementById("affectedDashboard").addEventListener("click", event => {
  const button = event.target.closest(".analysisBreakdownButton"); if (!button || appState !== APP_STATES.RESULTS) return;
  const states = selectedDrilldownSet(button.dataset.dimension), key = button.dataset.key, previousState = categoryState(states, key), nextState = previousState === CATEGORY_STATES.NEUTRAL ? CATEGORY_STATES.FOCUS : previousState === CATEGORY_STATES.FOCUS ? CATEGORY_STATES.EXCLUDE : CATEGORY_STATES.NEUTRAL, headlineBefore = document.getElementById("aboveThresholdCount").textContent;
  if (nextState === CATEGORY_STATES.NEUTRAL) states.delete(key); else states.set(key, nextState);
  updateAnalysisStats(); applyResultStyling();
  window.__drilldownInteractionAudit = { dimension: button.dataset.dimension, key, previousState, nextState, headlineBefore, headlineAfter: document.getElementById("aboveThresholdCount").textContent, displayedAffectedCount: window.__promptEffectsVisualAudit.displayedAffectedCount };
});
document.getElementById("clearDrilldownsBtn").addEventListener("click", () => { if (appState === APP_STATES.RESULTS) clearDrilldowns(); });
document.getElementById("copyShareLinkBtn").onclick = async event => { const copied = await copyText(buildShareUrl()), original = event.currentTarget.textContent; event.currentTarget.textContent = copied ? "Scenario link copied" : "Copy failed"; setTimeout(() => { event.currentTarget.textContent = original; }, 1500); };

function formatResultsPlaybackTime(seconds) {
  const totalMinutes = Math.max(0, Math.round(seconds / 60)), hours = Math.floor(totalMinutes / 60), minutes = totalMinutes % 60;
  return `${String(hours).padStart(2, "0")}:${String(minutes).padStart(2, "0")}`;
}

function updateResultsPlaybackControls() {
  const button = document.getElementById("resultsPlayBtn"), slider = document.getElementById("resultsTimelineSlider"), time = document.getElementById("resultsTimelineTime"), hours = resultPlaybackSeconds / 3600;
  button.innerHTML = `<span class="${resultsPlaybackPlaying ? "pauseIcon" : "playIcon"}"></span>`;
  button.setAttribute("aria-label", resultsPlaybackPlaying ? "Pause post-detonation movement" : "Play post-detonation movement");
  slider.value = Math.min(Number(slider.max), hours);
  slider.style.setProperty("--timeline-progress", `${Math.min(100, hours / Number(slider.max) * 100)}%`);
  time.textContent = formatResultsPlaybackTime(resultPlaybackSeconds);
  document.getElementById("resultsSpeedDownBtn").title = `Slow down · ${resultsPlaybackMultiplier.toFixed(2)}×`;
  document.getElementById("resultsSpeedUpBtn").title = `Speed up · ${resultsPlaybackMultiplier.toFixed(2)}×`;
}

document.getElementById("resultsPlayBtn").addEventListener("click", () => {
  if (appState !== APP_STATES.RESULTS) return;
  if (resultsPlaybackPlaying) { resultsPlaybackPlaying = false; updateResultsPlaybackControls(); return; }
  const before = captureRenderedIdentity(), frozenPositions = new Float32Array(points.geometry.attributes.position.array);
  updateResultSatellitePositions();
  const afterExactResume = captureRenderedIdentity(), exactResumePositionDelta = maximumPositionDelta(frozenPositions, points.geometry.attributes.position.array);
  resultPlaybackContinuityFrame = new Float32Array(points.geometry.attributes.position.array);
  window.__resultPlaybackIdentityAudit = { cycle: (window.__resultPlaybackCycleAudits?.length || 0) + 1, playbackSeconds: resultPlaybackSeconds, before, afterExactResume, exactResumePositionDelta, after: null };
  if (!window.__resultPlaybackCycleAudits) window.__resultPlaybackCycleAudits = [];
  window.__resultPlaybackCycleAudits.push(window.__resultPlaybackIdentityAudit);
  resultsPlaybackPlaying = true;
  if (!resultsHomeReturnStarted) { resultsHomeReturnStarted = true; beginResultsGlobeTransition(); }
  updateResultsPlaybackControls();
});
document.getElementById("resultsTimelineSlider").addEventListener("input", event => {
  if (appState !== APP_STATES.RESULTS) return;
  resultsPlaybackPlaying = false; resultPlaybackSeconds = Number(event.target.value) * 3600; simulationSeconds = resultDetonationSimulationSeconds + resultPlaybackSeconds;
  updateResultSatellitePositions(); updateResultsPlaybackControls();
});
document.getElementById("resultsSpeedDownBtn").addEventListener("click", () => { if (appState !== APP_STATES.RESULTS) return; resultsPlaybackMultiplier = Math.max(.25, resultsPlaybackMultiplier - .5); updateResultsPlaybackControls(); });
document.getElementById("resultsSpeedUpBtn").addEventListener("click", () => { if (appState !== APP_STATES.RESULTS) return; resultsPlaybackMultiplier = Math.min(4, resultsPlaybackMultiplier + .5); updateResultsPlaybackControls(); });

function closeScenarioInfo({ restoreFocus = false } = {}) {
  const popover = document.getElementById("scenarioInfoPopover"), button = document.getElementById("scenarioInfoBtn");
  if (!popover || popover.hidden) return;
  popover.hidden = true; button.setAttribute("aria-expanded", "false");
  if (restoreFocus) button.focus();
}
function openScenarioInfo() {
  if (appState !== APP_STATES.RESULTS) return;
  const popover = document.getElementById("scenarioInfoPopover"), button = document.getElementById("scenarioInfoBtn");
  popover.hidden = false; button.setAttribute("aria-expanded", "true"); document.getElementById("scenarioInfoCloseBtn").focus();
}
document.getElementById("scenarioInfoBtn").addEventListener("click", () => document.getElementById("scenarioInfoPopover").hidden ? openScenarioInfo() : closeScenarioInfo());
document.getElementById("scenarioInfoCloseBtn").addEventListener("click", () => closeScenarioInfo({ restoreFocus: true }));
document.addEventListener("keydown", event => { if (event.key === "Escape") closeScenarioInfo({ restoreFocus: true }); });
document.addEventListener("pointerdown", event => { const popover = document.getElementById("scenarioInfoPopover"); if (!popover.hidden && !popover.contains(event.target) && !document.getElementById("scenarioInfoBtn").contains(event.target)) closeScenarioInfo(); });

function resetPayloadEffects() {
  if (!points) return;
  const colors = points.geometry.attributes.effectColor.array, scales = points.geometry.attributes.effectScale.array, alphas = points.geometry.attributes.effectAlpha.array;
  for (let i = 0; i < scales.length; i++) { colors[i * 3] = colors[i * 3 + 1] = colors[i * 3 + 2] = .56; scales[i] = 1; alphas[i] = .48; }
  points.geometry.attributes.effectColor.needsUpdate = points.geometry.attributes.effectScale.needsUpdate = points.geometry.attributes.effectAlpha.needsUpdate = true;
  document.getElementById("fluenceResults").hidden = true;
  selectedAnalysisThreshold = 40; selectedCountryDrilldowns.clear(); selectedMissionDrilldowns.clear(); selectedConstellationDrilldowns.clear(); resultsPlaybackPlaying = false; resultsPlaybackMultiplier = 1; resultPlaybackSeconds = 0; resultFrameStart = NaN; resultFrame0 = resultFrame1 = null; resultPlaybackCatalogIds = []; resultVisualStates = []; resultPlaybackContinuityFrame = null; resultsHomeReturnStarted = false; thresholdNudgeShown = false; thresholdNudgeAnimation?.control?.removeAttribute("transform"); thresholdNudgeAnimation = null; cancelThresholdSlide(); timingAnalysisRunId++; timingAnalysisResult = null;
  afterglowStartedAt = null; scene.background.copy(SKY_BASE_COLOR); document.body.dataset.sky = "base"; document.getElementById("detonationWash").style.opacity = "0"; hideBlastCircle(); closeScenarioInfo();
  document.getElementById("satelliteTooltip").hidden = true;
  document.getElementById("countryBreakdown").replaceChildren(); document.getElementById("missionBreakdown").replaceChildren(); document.getElementById("constellationBreakdown").replaceChildren(); document.getElementById("clearDrilldownsBtn").disabled = true; updateResultsPlaybackControls();
  document.getElementById("resultsDisclosureBtn").setAttribute("aria-expanded", "false"); document.getElementById("resultsDetails").hidden = true; document.getElementById("timingAnalysisSummary").hidden = true; document.getElementById("timingBattle").hidden = true; document.getElementById("timingAnalysisStatus").textContent = ""; document.getElementById("timingAnalysisStatus").hidden = true;
  delete window.__resultPlaybackIdentityAudit; delete window.__resultPlaybackCycleAudits; delete window.__thresholdNudgeAudit; delete window.__headlineThresholdColorAudit; delete window.__legacyPlaybackDiscontinuityAudit; delete window.__resultsHomeTransitionAudit; delete window.__carrierStyleAudit;
  blastResults = null;
}

function updateBlastEffects(now, shellRadius) {
  if (!blastResults || !points) return;
  const colors = points.geometry.attributes.effectColor.array, scales = points.geometry.attributes.effectScale.array, alphas = points.geometry.attributes.effectAlpha.array, color = new THREE.Color();
  for (const record of blastResults.records) {
    const resultIndex = record.catalogIndex, index = renderIndexByCatalogId.get(record.catalogId); if (index === undefined) continue;
    if (!record.propagationValid || record.earthMasked) { scales[index] = 1; continue; }
    if (blastResults.distanceScene[resultIndex] > shellRadius) continue;
    if (blastResults.reachedAt[resultIndex] < 0) {
      blastResults.reachedAt[resultIndex] = now;
      fluenceColor(record.fluenceJm2, color);
      colors[index * 3] = color.r; colors[index * 3 + 1] = color.g; colors[index * 3 + 2] = color.b;
      alphas[index] = .98;
    }
    scales[index] = 1;
  }
  if (now - blastResults.lastHistogramUpdate > 240) { renderFluenceDensity(true); blastResults.lastHistogramUpdate = now; }
  points.geometry.attributes.effectColor.needsUpdate = points.geometry.attributes.effectAlpha.needsUpdate = points.geometry.attributes.effectScale.needsUpdate = true;
}
function wavefrontPointEarthBlocked(burst, point) { return segmentIntersectsSphere(burst.toArray(), point.toArray(), 1); }

function updateBlastCircle(progress, opacity) {
  if (!blastShell) return;
  const circle = document.getElementById("blastCircle"), projectedCenter = blastShell.position.clone().project(camera);
  const centerX = (projectedCenter.x * .5 + .5) * innerWidth, centerY = (-projectedCenter.y * .5 + .5) * innerHeight;
  const containedRadius = Math.max(2, Math.min(centerX, innerWidth - centerX, centerY, innerHeight - centerY) * .90), diameter = 2 * containedRadius * THREE.MathUtils.clamp(progress, 0, 1);
  circle.hidden = false; circle.style.left = `${centerX}px`; circle.style.top = `${centerY}px`; circle.style.width = circle.style.height = `${diameter}px`; circle.style.opacity = opacity.toFixed(4);
  window.__blastCircleGeometry = { centerX, centerY, diameter, containedRadius, equalDimensions: true };
}

function hideBlastCircle() { const circle = document.getElementById("blastCircle"); circle.hidden = true; circle.style.opacity = "0"; }
function createBlastField() { const anchor = new THREE.Object3D(); anchor.userData.screenSpaceDomCircle = true; return anchor; }
function disposeBlastField() { hideBlastCircle(); if (!blastShell) return; scene.remove(blastShell); blastShell = null; }

function applyStoredFluenceColors() {
  if (!blastResults || !points) return;
  const colors = points.geometry.attributes.effectColor.array, color = new THREE.Color();
  blastResults.records.forEach(record => {
    const index = renderIndexByCatalogId.get(record.catalogId); if (index === undefined) return;
    if (!record.propagationValid || record.earthMasked) color.setRGB(.36, .36, .36);
    else fluenceColor(record.fluenceJm2, color);
    colors[index * 3] = color.r; colors[index * 3 + 1] = color.g; colors[index * 3 + 2] = color.b;
  });
  points.geometry.attributes.effectColor.needsUpdate = true;
}

function createDetonationFlash(position, now) {
  disposeDetonationFlash();
  const group = new THREE.Group();
  const coreMaterial = new THREE.MeshBasicMaterial({ color: 0xfffbdf, transparent: true, opacity: 1, depthTest: true, depthWrite: false });
  const core = new THREE.Mesh(new THREE.SphereGeometry(1, 36, 28), coreMaterial); core.scale.setScalar(.018); core.renderOrder = 28; core.userData.flashPart = "core"; group.add(core);
  const canvas = document.createElement("canvas"); canvas.width = canvas.height = 128; const context = canvas.getContext("2d"), gradient = context.createRadialGradient(64, 64, 0, 64, 64, 63);
  gradient.addColorStop(0, "rgba(255,255,245,1)"); gradient.addColorStop(.16, "rgba(255,231,131,.95)"); gradient.addColorStop(.48, "rgba(234,170,0,.38)"); gradient.addColorStop(1, "rgba(234,170,0,0)"); context.fillStyle = gradient; context.fillRect(0, 0, 128, 128);
  const glowTexture = new THREE.CanvasTexture(canvas), glowMaterial = new THREE.SpriteMaterial({ map: glowTexture, transparent: true, opacity: 1, depthTest: true, depthWrite: false });
  const glow = new THREE.Sprite(glowMaterial); glow.scale.set(.18, .18, 1); glow.renderOrder = 27; glow.userData.flashPart = "glow"; group.add(glow);
  group.position.copy(position); group.userData.startedAt = now; scene.add(group); detonationFlash = group;
}

function updateDetonationFlash(now) {
  if (!detonationFlash) return;
  const progress = Math.min(1, (now - detonationFlash.userData.startedAt) / 2200), envelope = Math.sin(Math.PI * progress);
  const core = detonationFlash.children.find(child => child.userData.flashPart === "core"), glow = detonationFlash.children.find(child => child.userData.flashPart === "glow");
  core.scale.setScalar(.018 + .095 * envelope); core.material.opacity = Math.pow(1 - progress, .75);
  const glowScale = .18 + .34 * envelope; glow.scale.set(glowScale, glowScale, 1); glow.material.opacity = Math.pow(1 - progress, .62);
  if (progress === 1) disposeDetonationFlash();
}

function disposeDetonationFlash() {
  if (!detonationFlash) return;
  scene.remove(detonationFlash);
  detonationFlash.traverse(child => { if (child.geometry) child.geometry.dispose(); if (child.material?.map) child.material.map.dispose(); if (child.material) child.material.dispose(); });
  detonationFlash = null;
}

function carrierStyleSignature() {
  if (!carrierSprite) return null;
  return { baseScale: carrierSprite.userData.baseScale, scale: carrierSprite.scale.toArray(), color: carrierSprite.material.color.getHexString(), opacity: carrierSprite.material.opacity, mapUuid: carrierSprite.material.map?.uuid || null };
}

function triggerDetonation(now) {
  if (!detonationSequence || detonationSequence.triggered || !blastResults) return;
  window.__detonationAudit = { cameraMovingAtTrigger: Boolean(cameraTransition), elapsedMs: now - detonationSequence.startedAt, stationaryHoldMs: Math.max(0, now - detonationSequence.startedAt - COUNTDOWN_DURATION_MS), countdownHistory: [...detonationSequence.countdownHistory] };
  detonationSequence.triggered = true; blastShell = createBlastField(); blastShell.position.copy(detonationSequence.burstScene); blastShell.scale.setScalar(.001); scene.add(blastShell); createDetonationFlash(detonationSequence.burstScene, now);
  afterglowStartedAt = now; document.getElementById("detonationWash").style.opacity = "0"; scene.background.copy(SKY_AFTERGLOW_COLOR); document.body.dataset.sky = "afterglow";
  window.__blastVisualAudit = { wavefrontCount: 1, screenSpaceDomCircle: blastShell.userData.screenSpaceDomCircle, viewportContained: true, earthCropping: false, satelliteImpact: "fluence-color-on-contact", exposureColorsDuringWave: true, centralFlash: true, pulseDurationMs: BLAST_ANIMATION_DURATION_MS, afterglowHoldMs: AFTERGLOW_HOLD_MS, afterglowFadeMs: AFTERGLOW_FADE_MS, cinematicWash: { riseMs: DETONATION_WASH_RISE_MS, holdMs: DETONATION_WASH_HOLD_MS, fadeMs: DETONATION_WASH_FADE_MS, maximumOpacity: DETONATION_WASH_MAX_OPACITY } };
  showFluenceResults(); blastStartedAt = now; setAppState(APP_STATES.DETONATION); const button = document.getElementById("detonateBtn"); button.dataset.detonated = "true"; button.textContent = "Reset"; window.__promptEffectsResult = blastResults;
}

function beginDetonationSequence() {
  if (appState !== APP_STATES.RUNNING && appState !== APP_STATES.PAUSED) return;
  hideYieldPreview(); const yieldKt = Number(document.querySelector(".activeYield").dataset.yield), detonationEpoch = new Date(catalogEpoch.getTime() + simulationSeconds * 1000), detonationSimulationSeconds = (detonationEpoch.getTime() - catalogEpoch.getTime()) / 1000;
  simulationSeconds = detonationSimulationSeconds; carrierSprite.position.copy(carrierPosition(simulationSeconds)); trajectoryGroup.rotation.y = -EARTH_ROTATION_RATE_RAD_PER_SEC * simulationSeconds; const burstScene = carrierSprite.position.clone();
  const ordinaryCarrierScale = carrierSprite.userData.baseScale; carrierSprite.scale.set(ordinaryCarrierScale, ordinaryCarrierScale, 1); carrierPulseStartedAt = null;
  blastFinalScale = effectRadiusScene(yieldKt); blastResults = null;
  const sequence = { startedAt: performance.now(), burstScene, yieldKt, detonationEpoch, triggered: false, countdownHistory: ["3"], carrierStyleBefore: carrierStyleSignature() }; detonationSequence = sequence; resultsPlaybackPlaying = false; setAppState(APP_STATES.COUNTDOWN); setDetonationView(burstScene, COUNTDOWN_DURATION_MS); document.getElementById("detonateBtn").textContent = "3";
  prepareBlastResultsAsync(burstScene, yieldKt, detonationEpoch, detonationSimulationSeconds).then(result => { if (detonationSequence !== sequence) return; blastResults = result; blastWaveMaxScale = result.summary.maximumDistanceKm * SCALE; }).catch(error => { console.error(error); showLoadError(error); });
}

document.getElementById("detonateBtn").onclick = event => {
  const detonated = appState === APP_STATES.DETONATION || appState === APP_STATES.RESULTS;
  if (detonated) { event.currentTarget.dataset.detonated = "false"; event.currentTarget.innerHTML = '<span class="detonateGlyph"></span>Detonate'; blastStartedAt = null; detonationSequence = null; resetPayloadEffects(); updateSatellitePositions(true); setFullEarthView(); disposeBlastField(); disposeDetonationFlash(); setAppState(APP_STATES.RUNNING); }
  else beginDetonationSequence();
};

function scenePositionToGeodetic(position) { const radius = position.length(); return { latitudeDegrees: Number(THREE.MathUtils.radToDeg(Math.asin(position.y / radius)).toFixed(6)), longitudeDegrees: Number(THREE.MathUtils.radToDeg(Math.atan2(-position.z, position.x)).toFixed(6)), altitudeKm: Number(((radius - 1) * EARTH_RADIUS_KM).toFixed(3)) }; }

addEventListener("resize",()=>{camera.aspect=innerWidth/innerHeight; renderer.setSize(innerWidth,innerHeight); camera.updateProjectionMatrix(); apply3DViewOffset(); refreshDetonationViewForLayout(); positionSearchResults();});
makeFallbackEarth(); setFullEarthView(); setAppState(APP_STATES.LOADING);
loadWorldBoundaries().catch(error => console.error(error));
loadCatalog().catch(error => { console.error(error); showLoadError(error); });

function animate() {
  requestAnimationFrame(animate);
  const now = performance.now(), dt = (now - lastFrameTime) / 1000; lastFrameTime = now;
  if (points && populationRevealStartedAt !== null) points.material.uniforms.revealOpacity.value = Math.min(1, (now - populationRevealStartedAt) / 700);
  if (carrierTrajectory && carrierDrawStartedAt !== null) { const progress = Math.min(1, (now - carrierDrawStartedAt) / 1200), eased = 1 - Math.pow(1 - progress, 3); carrierTrajectory.children.filter(object => object !== carrierShimmer).forEach(object => object.geometry.setDrawRange(0, Math.floor(object.userData.fullDrawCount * eased))); if (progress === 1) carrierDrawStartedAt = null; }
  if (carrierShimmer && carrierShimmerStartedAt !== null) { const progress = Math.min(1, (now - carrierShimmerStartedAt) / 1750), full = carrierShimmer.userData.fullDrawCount, segment = Math.max(12, Math.floor(full * .09)), start = Math.floor(progress * Math.max(1, full - segment)); carrierShimmer.geometry.setDrawRange(start, segment); carrierShimmer.material.opacity = Math.sin(Math.PI * progress) * .95; if (progress === 1) { carrierShimmer.material.opacity = 0; carrierShimmerStartedAt = null; } }
  if (carrierSprite && appState === APP_STATES.RUNNING) { if (carrierPulseStartedAt === null && now >= nextCarrierPulseAt) carrierPulseStartedAt = now; if (carrierPulseStartedAt !== null) { const progress = Math.min(1, (now - carrierPulseStartedAt) / 850), pulse = 1 + .20 * Math.pow(Math.sin(Math.PI * progress), 2), scale = carrierSprite.userData.baseScale * pulse; carrierSprite.scale.set(scale, scale, 1); if (progress === 1) { carrierPulseStartedAt = null; nextCarrierPulseAt = now + 4200 + Math.random() * 2600; } } }
  if (isPlaying) { simulationSeconds += dt * BASE_PLAYBACK_SIM_HOURS_PER_REAL_SECOND * playbackMultiplier * 3600; if (simulationSeconds > 86400) simulationSeconds = 0; if (points) updateSatellitePositions(); else if (carrierSprite) { carrierSprite.position.copy(carrierPosition(simulationSeconds)); if (yieldPreview) yieldPreview.position.copy(carrierSprite.position); trajectoryGroup.rotation.y = -EARTH_ROTATION_RATE_RAD_PER_SEC * simulationSeconds; } }
  if (appState === APP_STATES.RESULTS && resultsPlaybackPlaying) {
    resultPlaybackSeconds = Math.min(24 * 3600, resultPlaybackSeconds + dt * RESULTS_PLAYBACK_SIM_SECONDS_PER_REAL_SECOND * resultsPlaybackMultiplier);
    simulationSeconds = resultDetonationSimulationSeconds + resultPlaybackSeconds; updateResultSatellitePositions();
    if (resultPlaybackSeconds >= 24 * 3600) resultsPlaybackPlaying = false;
    updateResultsPlaybackControls();
  }
  if (appState === APP_STATES.RUNNING && !anomalyEditing) { const anomaly = wrapDegrees(carrierTrueAnomalyAt(simulationSeconds)); document.getElementById("anomalySlider").value = anomaly; document.getElementById("anomalyValue").textContent = `${anomaly.toFixed(1)}°`; }
  if (yieldPreview && yieldPreviewPuffStartedAt !== null) { const progress = Math.min(1, (now - yieldPreviewPuffStartedAt) / 900), eased = 1 - Math.pow(1 - progress, 3), scale = yieldPreview.userData.targetScale * (.08 + 1.02 * eased); yieldPreview.scale.setScalar(scale); yieldPreview.traverse(child => { if (child.material) child.material.opacity = child.material.userData.baseOpacity * Math.pow(1 - progress, .7); }); if (progress === 1) hideYieldPreview(); }
  updateThresholdNudge(now);
  updateCameraTransition(now);
  updateDetonationFlash(now);
  if (detonationSequence && !detonationSequence.triggered) { const elapsed = now - detonationSequence.startedAt, remaining = Math.max(1, 3 - Math.floor(elapsed / 1000)), label = blastResults || elapsed < COUNTDOWN_DURATION_MS + POST_CAMERA_HOLD_MS ? String(remaining) : "…"; document.getElementById("detonateBtn").textContent = label; if (label !== "…" && detonationSequence.countdownHistory.at(-1) !== label) detonationSequence.countdownHistory.push(label); if (elapsed >= COUNTDOWN_DURATION_MS + POST_CAMERA_HOLD_MS && !cameraTransition && blastResults) triggerDetonation(now); }
  if (blastShell && blastStartedAt !== null) {
    const elapsed = now - blastStartedAt, progress = Math.min(1, elapsed / BLAST_ANIMATION_DURATION_MS), eased = 1 - Math.pow(1 - progress, 3), shellRadius = Math.max(.001, blastWaveMaxScale * eased);
    blastShell.scale.setScalar(shellRadius);
    updateBlastCircle(eased, .94 * Math.pow(1 - progress, .7));
    if (appState === APP_STATES.DETONATION) updateBlastEffects(now, shellRadius);
    if (progress === 1 && appState === APP_STATES.DETONATION) {
      const baseScale = carrierSprite.userData.baseScale; carrierSprite.scale.set(baseScale, baseScale, 1);
      applyStoredFluenceColors(); applyResultStyling(); renderFluenceDensity(false); updateAnalysisStats(); setAppState(APP_STATES.RESULTS); resultsPlaybackPlaying = false; updateResultsPlaybackControls(); requestAnimationFrame(startThresholdNudge); blastStartedAt = null; disposeBlastField(); disposeDetonationFlash();
      window.__carrierStyleAudit = { before: detonationSequence?.carrierStyleBefore || null, after: carrierStyleSignature() };
    }
  }
  if (afterglowStartedAt !== null) {
    const elapsed = now - afterglowStartedAt;
    const wash = document.getElementById("detonationWash"), washHoldEnd = DETONATION_WASH_RISE_MS + DETONATION_WASH_HOLD_MS, washEnd = washHoldEnd + DETONATION_WASH_FADE_MS;
    let washOpacity = 0;
    if (elapsed < DETONATION_WASH_RISE_MS) washOpacity = DETONATION_WASH_MAX_OPACITY * (1 - Math.pow(1 - elapsed / DETONATION_WASH_RISE_MS, 3));
    else if (elapsed <= washHoldEnd) washOpacity = DETONATION_WASH_MAX_OPACITY;
    else if (elapsed < washEnd) washOpacity = DETONATION_WASH_MAX_OPACITY * Math.pow(1 - (elapsed - washHoldEnd) / DETONATION_WASH_FADE_MS, 1.25);
    wash.style.opacity = washOpacity.toFixed(4);
    if (elapsed <= AFTERGLOW_HOLD_MS) { scene.background.copy(SKY_AFTERGLOW_COLOR); document.body.dataset.sky = "afterglow"; }
    else if (elapsed < AFTERGLOW_HOLD_MS + AFTERGLOW_FADE_MS) { scene.background.copy(SKY_AFTERGLOW_COLOR).lerp(SKY_BASE_COLOR, (elapsed - AFTERGLOW_HOLD_MS) / AFTERGLOW_FADE_MS); document.body.dataset.sky = "fading"; }
    else { scene.background.copy(SKY_BASE_COLOR); document.body.dataset.sky = "base"; wash.style.opacity = "0"; afterglowStartedAt = null; }
  }
  updateCarrierTracking(now, dt); controls.update(); renderer.render(scene, camera);
}
animate();
