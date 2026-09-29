-- Prove2me | Theorems.Thm_F1Tightness_one_add_flatDist_le_gapX
-- name    : F1Tightness.one_add_flatDist_le_gapX
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:26:51.969054+00:00
-- url     : https://prove2.me/theorems/98f6f56c-1e05-4269-9e2c-9b99ff498ef5
-- title:
--   The quantitative slack.
-- statement:
--   **The quantitative slack.**  The gap factor exceeds one by at least the L¹
--   distance to flatness, normalised by `2M`.
--
--   ```lean
--   theorem F1Tightness.one_add_flatDist_le_gapX{p : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
--       (hsum : ∑ i : Fin M, p i = 1) (hanti : Antitone p) :
--       1 + flatDist p / (2 * (M : ℝ)) ≤ gapX p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessQuantitative.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessQuantitative.lean#L147

-- Thm stub generated from Probability/F1TightnessQuantitative.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative

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

open F1Tightness

open Finset

variable {M : ℕ}

theorem F1Tightness.one_add_flatDist_le_gapX{p : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin M, p i = 1) (hanti : Antitone p) :
    1 + flatDist p / (2 * (M : ℝ)) ≤ gapX p := by sorry
