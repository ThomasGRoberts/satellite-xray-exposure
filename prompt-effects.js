export const X_RAY_YIELD_FRACTION = 0.70;
export const JOULES_PER_KILOTON = 4.184e12;
export const PERMANENT_DAMAGE_THRESHOLD_J_M2 = 40;

export function xrayFluenceJm2(yieldKt, distanceMeters) {
  if (!(yieldKt >= 0) || !(distanceMeters > 0)) return distanceMeters === 0 && yieldKt > 0 ? Infinity : 0;
  return X_RAY_YIELD_FRACTION * yieldKt * JOULES_PER_KILOTON / (4 * Math.PI * distanceMeters * distanceMeters);
}

export function thresholdRadiusMeters(yieldKt, thresholdJm2 = PERMANENT_DAMAGE_THRESHOLD_J_M2) {
  if (!(yieldKt >= 0) || !(thresholdJm2 > 0)) return 0;
  return Math.sqrt(X_RAY_YIELD_FRACTION * yieldKt * JOULES_PER_KILOTON / (4 * Math.PI * thresholdJm2));
}

// Camera-independent closest-point test on the finite burst-to-payload segment.
export function segmentIntersectsSphere(startKm, endKm, radiusKm) {
  const dx = endKm[0] - startKm[0], dy = endKm[1] - startKm[1], dz = endKm[2] - startKm[2];
  const lengthSquared = dx * dx + dy * dy + dz * dz;
  if (!(lengthSquared > 0)) return false;
  const t = Math.max(0, Math.min(1, -(startKm[0] * dx + startKm[1] * dy + startKm[2] * dz) / lengthSquared));
  const x = startKm[0] + t * dx, y = startKm[1] + t * dy, z = startKm[2] + t * dz;
  return x * x + y * y + z * z <= radiusKm * radiusKm;
}

export function calculatePromptExposure({ catalog, positionsEciKm, burstEciKm, yieldKt, earthRadiusKm }) {
  if (positionsEciKm.length !== catalog.length * 3) throw new Error("Propagated-position count does not match catalog count");
  const records = new Array(catalog.length);
  let earthMaskedCount = 0, directCount = 0, aboveThresholdCount = 0, invalidCount = 0;
  let minimumPositiveFluence = Infinity, maximumFluence = 0, maximumDistanceKm = 0;

  for (let index = 0; index < catalog.length; index++) {
    const offset = index * 3;
    const positionEciKm = [positionsEciKm[offset], positionsEciKm[offset + 1], positionsEciKm[offset + 2]];
    const valid = positionEciKm.every(Number.isFinite);
    if (!valid) {
      invalidCount++;
      records[index] = {
        catalogIndex: index,
        catalogId: String(catalog[index].NORAD_CAT_ID),
        cosparId: catalog[index].OBJECT_ID || "",
        name: catalog[index].OBJECT_NAME || "",
        ownerCode: catalog[index].OWNER || "Unknown",
        missionClassCode: catalog[index].GCAT_CLASS || "",
        missionClass: catalog[index].MISSION_CLASS || "Unclassified",
        missionClasses: catalog[index].MISSION_CLASSES || [],
        gcatMatched: Boolean(catalog[index].GCAT_MATCHED),
        positionEciKm,
        distanceKm: null,
        earthMasked: null,
        fluenceJm2: null,
        thresholds: { fangMoricPermanentDamage40Jm2: false },
        propagationValid: false
      };
      continue;
    }

    const dx = positionEciKm[0] - burstEciKm[0], dy = positionEciKm[1] - burstEciKm[1], dz = positionEciKm[2] - burstEciKm[2];
    const distanceKm = Math.hypot(dx, dy, dz);
    const earthMasked = segmentIntersectsSphere(burstEciKm, positionEciKm, earthRadiusKm);
    const fluenceJm2 = earthMasked ? 0 : xrayFluenceJm2(yieldKt, distanceKm * 1000);
    const exceedsThreshold = !earthMasked && fluenceJm2 >= PERMANENT_DAMAGE_THRESHOLD_J_M2;
    maximumDistanceKm = Math.max(maximumDistanceKm, distanceKm);
    if (earthMasked) earthMaskedCount++;
    else {
      directCount++;
      if (fluenceJm2 > 0 && Number.isFinite(fluenceJm2)) minimumPositiveFluence = Math.min(minimumPositiveFluence, fluenceJm2);
      maximumFluence = Math.max(maximumFluence, fluenceJm2);
      if (exceedsThreshold) aboveThresholdCount++;
    }
    records[index] = {
      catalogIndex: index,
      catalogId: String(catalog[index].NORAD_CAT_ID),
      cosparId: catalog[index].OBJECT_ID || "",
      name: catalog[index].OBJECT_NAME || "",
      ownerCode: catalog[index].OWNER || "Unknown",
      missionClassCode: catalog[index].GCAT_CLASS || "",
      missionClass: catalog[index].MISSION_CLASS || "Unclassified",
      missionClasses: catalog[index].MISSION_CLASSES || [],
      gcatMatched: Boolean(catalog[index].GCAT_MATCHED),
      positionEciKm,
      distanceKm,
      earthMasked,
      fluenceJm2,
      thresholds: { fangMoricPermanentDamage40Jm2: exceedsThreshold },
      propagationValid: true
    };
  }

  return {
    model: {
      xrayYieldFraction: X_RAY_YIELD_FRACTION,
      joulesPerKiloton: JOULES_PER_KILOTON,
      thresholdJm2: PERMANENT_DAMAGE_THRESHOLD_J_M2,
      earthMaskRadiusKm: earthRadiusKm
    },
    records,
    summary: {
      totalCount: catalog.length,
      directCount,
      earthMaskedCount,
      aboveThresholdCount,
      invalidCount,
      minimumPositiveFluence: Number.isFinite(minimumPositiveFluence) ? minimumPositiveFluence : 0,
      maximumFluence,
      maximumDistanceKm
    }
  };
}
