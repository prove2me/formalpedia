-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_geometric_scaling_lower
-- name    : Catalog.MachineLearning.NoiseFloor.geometric_scaling_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:12.777668+00:00
-- url     : https://prove2.me/theorems/520d78f2-b176-4c9a-b394-653e433c12fe
-- title:
--   Lower scaling bound.
-- statement:
--   **Lower scaling bound.**  If the mode `m` is still above the noise level,
--   then at least `m+1` modes are resolvable and each costs `b/2`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.geometric_scaling_lower(hr0 : 0 < r) (hr1 : r < 1) (hb : 0 < b) {n m : ℕ}
--       (hmn : m + 1 ≤ n) (hbm : b ≤ r ^ m) :
--       b * (m + 1) / 2 ≤ noiseFloor (fun i : Fin n => r ^ (i : ℕ)) b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/SpectralScalingLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/SpectralScalingLaw.lean#L103

-- Thm stub generated from MachineLearning/NoiseFloor/SpectralScalingLaw.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part VIII: a formal scaling law

Round-6 hypothesis closure, Phase A, cycle 5.

Neural scaling laws assert that the irreducible risk of a model decays like a
power (or a power times a log) of the amount of data.  Parts I–VII reduce the
irreducible risk to the single functional `noiseFloor a b`, so a scaling law is
now a *computation with a fixed spectrum*, not a modelling assumption.

We carry this out for the geometric (exponentially decaying) spectrum
`a i = r ^ i`, `0 < r < 1`, at noise level `b = σ²/N`.  The head/tail sandwich
of Part IV yields matching bounds

  `b (m+1) / 2  ≤  noiseFloor  ≤  b (m+1) + r^{m+1} / (1 - r)`

for every cut index `m`, and taking the natural cut `r^{m+1} ≤ b ≤ r^m` gives

  `b (m+1) / 2  ≤  noiseFloor  ≤  b (m+1) + b / (1 - r)`,

i.e. `noiseFloor ≍ b · m ≍ b · log(1/b) / log(1/r)`: **the log-corrected `1/N`
law**, derived rather than assumed.

## Main results

* `noiseFloor_geom_eq`        — the floor of a geometric spectrum as a range sum
* `geometric_scaling_upper`   — upper bound for every cut `m`
* `geometric_scaling_lower`   — matching lower bound when `b ≤ r^m`
* `geometric_scaling_law`     — the two-sided law at the natural cut
-/

open Catalog.MachineLearning.NoiseFloor

open Finset


variable {r b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.geometric_scaling_lower(hr0 : 0 < r) (hr1 : r < 1) (hb : 0 < b) {n m : ℕ}
    (hmn : m + 1 ≤ n) (hbm : b ≤ r ^ m) :
    b * (m + 1) / 2 ≤ noiseFloor (fun i : Fin n => r ^ (i : ℕ)) b := by sorry
