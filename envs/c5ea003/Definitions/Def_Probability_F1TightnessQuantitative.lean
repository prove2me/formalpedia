-- Prove2me | Definitions.Def_Probability_F1TightnessQuantitative
-- name    : Probability_F1TightnessQuantitative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:37.494046+00:00
-- url     : https://prove2.me/theorems/283b8e62-73ee-43aa-ba17-4ab253435853
-- title:
--   Aether Catalog definitions — Probability_F1TightnessQuantitative
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessQuantitative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessQuantitative.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# A quantitative (L¹) strengthening of the F1 master inequality

`Probability.F1TightnessCore` proves that on an antitone non-flat profile the
slack factor `X = C₀/c_asc` is strictly larger than one, so the master bound is
never attained; but `one_lt_gapX` is qualitative — it gives no number.

This file supplies the number.  Write

`flatDist p = ∑ i, |p i − 1/M|`

for the L¹ distance of the profile to the flat profile.  Then, for every
antitone profile,

* `scanCost_le_baseCost_sub_flatDist` — `c_asc ≤ C₀ − ‖p − flat‖₁ / 2`;
* `one_add_flatDist_le_gapX` — `1 + ‖p − flat‖₁/(2M) ≤ X`;
* `speedup_mul_le_bound_quantitative` — **the refined master inequality**
  `S · (1 + ‖p − flat‖₁/(2M)) ≤ bound`, i.e. `S ≤ bound/(1 + V)` with the
  explicit, computable dispersion functional `V = ‖p − flat‖₁/(2M)`;
* `flatDist_eq_zero_iff` — `V` vanishes exactly on the flat profile, the case
  the three independent tests reject pool-side.

The proof route is the pairwise expansion `sum_pairs_identity` of the core file,
kept with its quadratic remainder instead of discarded: for an antitone profile
each pairwise term of the Chebyshev double sum is bounded below by `|p i − p j|`
in absolute value, and the triangle inequality converts the resulting double sum
into the L¹ distance to flat.  This is the shape asked for by direction 3 of
`FUTURE_DIRECTIONS.md`, with the absolute constant `c = 1` in the normalisation
`V = ‖p − flat‖₁/(2M)`.
-/

namespace F1Tightness

open Finset

variable {M : ℕ}

/-- L¹ distance of the profile to the flat profile. -/
noncomputable def flatDist (p : Fin M → ℝ) : ℝ := ∑ i : Fin M, |p i - (M : ℝ)⁻¹|










/-! ## Non-vacuity: an explicit profile with a positive dispersion -/

/-- The two-cell profile `(3/4, 1/4)`. -/
noncomputable def demoTwo : Fin 2 → ℝ := ![3 / 4, 1 / 4]






end F1Tightness


