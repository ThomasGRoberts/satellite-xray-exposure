import * as satellite from "./vendor/satellite.es.js";
import { calculatePromptExposure } from "./prompt-effects.js";

let catalog = [];
let satrecs = [];

self.onmessage = event => {
  const message = event.data;
  if (message.type === "initialize") {
    catalog = message.catalog;
    satrecs = catalog.map(row => satellite.json2satrec(row));
    self.postMessage({ type: "ready" });
    return;
  }
  if (message.type !== "calculate") return;

  const epoch = new Date(message.epoch), gmst = satellite.gstime(epoch), positionsEciKm = new Float64Array(catalog.length * 3), velocitiesEciKmS = new Float64Array(catalog.length * 3), sceneFrame = new Float32Array(catalog.length * 3);
  positionsEciKm.fill(NaN); velocitiesEciKmS.fill(NaN); sceneFrame.fill(NaN);
  let validCount = 0;
  for (let index = 0; index < satrecs.length; index++) {
    const state = satellite.propagate(satrecs[index], epoch), position = state && state.position, velocity = state && state.velocity;
    if (!position || !velocity || !Number.isFinite(position.x) || !Number.isFinite(position.y) || !Number.isFinite(position.z) || !Number.isFinite(velocity.x) || !Number.isFinite(velocity.y) || !Number.isFinite(velocity.z)) continue;
    const offset = index * 3, fixed = satellite.eciToEcf(position, gmst);
    positionsEciKm[offset] = position.x; positionsEciKm[offset + 1] = position.y; positionsEciKm[offset + 2] = position.z;
    velocitiesEciKmS[offset] = velocity.x; velocitiesEciKmS[offset + 1] = velocity.y; velocitiesEciKmS[offset + 2] = velocity.z;
    sceneFrame[offset] = fixed.x / message.earthRadiusKm; sceneFrame[offset + 1] = fixed.z / message.earthRadiusKm; sceneFrame[offset + 2] = -fixed.y / message.earthRadiusKm;
    validCount++;
  }
  const result = calculatePromptExposure({ catalog, positionsEciKm, burstEciKm: message.burstEciKm, yieldKt: message.yieldKt, earthRadiusKm: message.earthRadiusKm });
  const distanceKm = new Float64Array(catalog.length), fluenceJm2 = new Float64Array(catalog.length), earthMasked = new Uint8Array(catalog.length), propagationValid = new Uint8Array(catalog.length), exceeds40 = new Uint8Array(catalog.length);
  result.records.forEach((record, index) => { distanceKm[index] = record.distanceKm ?? NaN; fluenceJm2[index] = record.fluenceJm2 ?? NaN; earthMasked[index] = record.earthMasked ? 1 : 0; propagationValid[index] = record.propagationValid ? 1 : 0; exceeds40[index] = record.thresholds.fangMoricPermanentDamage40Jm2 ? 1 : 0; });
  self.postMessage({ type: "result", requestId: message.requestId, model: result.model, summary: result.summary, positionsEciKm, velocitiesEciKmS, sceneFrame, distanceKm, fluenceJm2, earthMasked, propagationValid, exceeds40, validCount }, [positionsEciKm.buffer, velocitiesEciKmS.buffer, sceneFrame.buffer, distanceKm.buffer, fluenceJm2.buffer, earthMasked.buffer, propagationValid.buffer, exceeds40.buffer]);
};
