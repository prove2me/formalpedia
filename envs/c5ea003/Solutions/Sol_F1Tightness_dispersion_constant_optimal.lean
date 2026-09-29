-- Prove2me | solution 1 for F1Tightness.dispersion_constant_optimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:50:54.482919+00:00
-- url     : https://prove2.me/submissions/caf23a03-5ad3-4a50-ae7e-0b8d39429436

-- Sol generated from Probability/F1TightnessDispersion.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative
import Definitions.Def_Probability_F1TightnessSharpness
import Theorems.Thm_F1Tightness_twoCell_antitone
import Theorems.Thm_F1Tightness_twoCell_gapX
import Theorems.Thm_F1Tightness_twoCell_nonneg
import Theorems.Thm_F1Tightness_twoCell_scanCost
import Theorems.Thm_F1Tightness_twoCell_sum

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

theorem twoCell_flatDist {δ : ℝ} (h0 : 0 ≤ δ) : flatDist (twoCell δ) = 2 * δ := by
  have h : flatDist (twoCell δ) = |1 / 2 + δ - 2⁻¹| + |1 / 2 - δ - 2⁻¹| := by
    rw [flatDist, Fin.sum_univ_two]
    norm_num [twoCell]
  rw [h]
  rw [show (1 : ℝ) / 2 + δ - 2⁻¹ = δ by ring, show (1 : ℝ) / 2 - δ - 2⁻¹ = -δ by ring,
    abs_of_nonneg h0, abs_neg, abs_of_nonneg h0]
  ring

/-- **Exactness on two cells.**  For the two-cell family the sharper dispersion
inequality holds with equality. -/
theorem twoCell_dispersion_exact {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1 / 2) :
    gapX (twoCell δ) = 1 + flatDist (twoCell δ) / (2 * scanCost (twoCell δ)) := by
  have hc : scanCost (twoCell δ) = 3 / 2 - δ := twoCell_scanCost δ
  have hcpos : (0 : ℝ) < 3 / 2 - δ := by linarith
  have hne : (3 / 2 : ℝ) - δ ≠ 0 := ne_of_gt hcpos
  have h2 : (2 : ℝ) * δ / (2 * (3 / 2 - δ)) = δ / (3 / 2 - δ) :=
    mul_div_mul_left δ (3 / 2 - δ) two_ne_zero
  have hne2 : (3 : ℝ) - δ * 2 ≠ 0 := fun h => hne (by linarith)
  have h3 : (1 : ℝ) + δ / (3 / 2 - δ) = (3 / 2) / (3 / 2 - δ) := by
    field_simp
    ring
  rw [twoCell_gapX, twoCell_flatDist h0, hc, h2, h3]



open F1Tightness in
theorem solution{c : ℝ} (hc : 1 < c) :
    ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i : Fin 2, p i = 1) ∧ Antitone p ∧
      gapX p < 1 + c * (flatDist p / (2 * scanCost p)) := by
  refine ⟨twoCell (1 / 4), twoCell_nonneg (by norm_num) (by norm_num), twoCell_sum _,
    twoCell_antitone (by norm_num), ?_⟩
  have heq := twoCell_dispersion_exact (δ := 1 / 4) (by norm_num) (by norm_num)
  have hD : flatDist (twoCell (1 / 4 : ℝ)) = 1 / 2 := by
    rw [twoCell_flatDist (by norm_num)]; norm_num
  have hs : scanCost (twoCell (1 / 4 : ℝ)) = 5 / 4 := by
    rw [twoCell_scanCost]; norm_num
  rw [hD, hs] at heq ⊢
  rw [heq]
  have : (0 : ℝ) < 1 / 2 / (2 * (5 / 4)) := by norm_num
  nlinarith
