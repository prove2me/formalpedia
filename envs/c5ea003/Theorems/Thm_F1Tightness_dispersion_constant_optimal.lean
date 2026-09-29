-- Prove2me | Theorems.Thm_F1Tightness_dispersion_constant_optimal
-- name    : F1Tightness.dispersion_constant_optimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:55.58002+00:00
-- url     : https://prove2.me/theorems/ba09ec59-f53e-418e-b73a-9f11287e97cc
-- title:
--   Optimality of the constant.
-- statement:
--   **Optimality of the constant.**  No constant `c > 1` can be inserted in the
--   dispersion correction: the two-cell profiles already achieve equality, so the
--   inequality `1 + c·‖p − flat‖₁/(2·c_asc) ≤ X` fails for them.
--
--   ```lean
--   theorem F1Tightness.dispersion_constant_optimal{c : ℝ} (hc : 1 < c) :
--       ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i : Fin 2, p i = 1) ∧ Antitone p ∧
--         gapX p < 1 + c * (flatDist p / (2 * scanCost p)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessDispersion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessDispersion.lean#L100

-- Thm stub generated from Probability/F1TightnessDispersion.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative
import Definitions.Def_Probability_F1TightnessSharpness

/-!
# The optimal normalisation of the dispersion correction

`Probability.F1TightnessQuantitative` proved the refined master inequality
`S · (1 + ‖p − flat‖₁/(2M)) ≤ bound`, with the dispersion functional normalised
by `2M`.  Direction 2 of `FUTURE_DIRECTIONS.md` asks whether that normalisation
is optimal, and in particular whether the `2M` can be replaced by the strictly
smaller `2·c_asc` that the proof actually supplies.  This file answers both
questions.

* `one_add_flatDist_div_scanCost_le_gapX` — the **sharper** form
  `1 + ‖p − flat‖₁/(2·c_asc) ≤ X`;
* `flatDist_div_card_le_div_scanCost` — the sharper form dominates the booked
  one, because `c_asc ≤ M`;
* `speedup_mul_le_bound_dispersion` — the corresponding refinement of the master
  inequality;
* `twoCell_dispersion_exact` — on the two-cell family the sharper inequality is
  an **identity**: `X = 1 + ‖p − flat‖₁/(2·c_asc)`;
* `dispersion_constant_optimal` — consequently no constant `c > 1` is admissible
  in `1 + c·‖p − flat‖₁/(2·c_asc) ≤ X`, so the constant `1` is optimal and the
  extremal profiles are supported on two cells, exactly as conjectured.
-/

open F1Tightness

open Finset

variable {M : ℕ}




/-! ## The two-cell family makes the sharper inequality an identity -/

theorem F1Tightness.dispersion_constant_optimal{c : ℝ} (hc : 1 < c) :
    ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i : Fin 2, p i = 1) ∧ Antitone p ∧
      gapX p < 1 + c * (flatDist p / (2 * scanCost p)) := by sorry
