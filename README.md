# Prompt Effects Satellite Visualization

Corrected preview: `python3 -m http.server 8765 --bind 127.0.0.1`

Untouched reference comparison: `cd reference-original && python3 -m http.server 8764 --bind 127.0.0.1`

The corrected application directly reuses the supplied ESPL Three.js scene, high-resolution sphere, country-boundary tubes, OrbitControls camera, full-Earth/horizon camera treatments, view offset, satellite texture, orbit tube, playback controls, control panel, legend, logo, spacing, palette, and typography. The reference source contains no separate graticule implementation.

The catalog is a timestamped CelesTrak active GP snapshot joined to CelesTrak SATCAT by NORAD catalog ID and filtered to SATCAT `OBJECT_TYPE == PAY`. Raw source files, the filtered snapshot, checksum, source queries, retrieval time, counts, and element-epoch range are in `data/catalog/`. There is no synthetic catalog data in the corrected app. The animated display uses smooth, unperturbed two-body propagation from each OMM epoch; detonation analytics use SGP4 for the exact selected epoch in a background worker.

Mission class is prepared offline from GCAT `psatcat.tsv` and `psatcat100k.tsv`, joined only by normalized exact COSPAR ID (`OBJECT_ID` to `Piece`). Original GCAT codes remain in each prepared row; interface categories map A/C to Civil, B to Commercial, and D to Military, retaining every applicable category for combined codes. The current prepared snapshot uses GCAT release 1.8.8, data update 2026-09-16: 16,540/16,557 records matched and 16,534 have a usable class. It contains 1,165 Civil, 14,522 Commercial, 861 Military, 14 overlapping, and 23 unclassified payloads. Raw GCAT tables, checksums, unmatched IDs, unclassified IDs, original class codes, normalized categories, citation, and CC BY 4.0 attribution are archived in `data/catalog/` and `catalog-metadata.json`.

To prepare a fresh orbital snapshot and GCAT enrichment together:

`python3 scripts/build_catalog_snapshot.py ACTIVE_GP.json SATCAT.csv data/catalog RETRIEVAL_UTC`

The script downloads the current GCAT payload tables, records release metadata, performs the exact-COSPAR join, and writes validation coverage into the snapshot metadata.

Run verification with `python3 -m unittest discover -s tests -v`.

Approved camera exports are preserved as regression fixtures in `data/camera-calibration-examples.json`. The post-detonation camera rule uses their relative Earth/carrier geometry and full-viewport projection rather than replaying any absolute Earth-fixed camera position.
