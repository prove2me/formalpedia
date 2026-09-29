-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.actual_numerator_two_sided_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:14:15.026188+00:00
-- url     : https://prove2.me/submissions/4ee536f5-6dfe-41b9-9a03-eac756b91fc1

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_mem_literalTriangle_iff
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangleLogPoint_eq_log
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_triangle_card_le_actual_numerator
import Theorems.Thm_ErdosProblems_Erdos269_dyadicOrderedBlockDigit235_le_quadratic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact logarithmic coordinates and the paper's rectangle lower bound. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators









theorem mem_literalTriangle_log_iff {a : ℕ} {v : ℕ × ℕ} :
    v ∈ literalTriangle a ↔ triangleLogPoint v < (a : ℝ) + 1 := by
  rw [mem_literalTriangle_iff, triangleLogPoint_eq_log]
  have hm : (0 : ℝ) < triangleOddPart v := by unfold triangleOddPart; positivity
  have h := Real.logb_lt_iff_lt_rpow (y := (a : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hm
  rw [show (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] at h
  exact (by exact_mod_cast h.symm)



















theorem triangle_rectangle_subset (a : ℕ) :
    (Finset.range (triangleRectangleSide a 3)).product
      (Finset.range (triangleRectangleSide a 5)) ⊆ literalTriangle a := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hj, hk⟩
  have h3 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 5)
  have hjn : v.1 ≤ ⌊(a : ℝ) / (2 * Real.logb 2 3)⌋₊ := by
    have := Finset.mem_range.mp hj
    simp only [triangleRectangleSide, Nat.cast_ofNat] at this
    omega
  have hkn : v.2 ≤ ⌊(a : ℝ) / (2 * Real.logb 2 5)⌋₊ := by
    have := Finset.mem_range.mp hk
    simp only [triangleRectangleSide, Nat.cast_ofNat] at this
    omega
  have hjR := (Nat.le_floor_iff (by positivity : 0 ≤ (a : ℝ) / (2 * Real.logb 2 3))).mp hjn
  have hkR := (Nat.le_floor_iff (by positivity : 0 ≤ (a : ℝ) / (2 * Real.logb 2 5))).mp hkn
  have hjb := (le_div_iff₀ (by positivity : 0 < 2 * Real.logb 2 3)).mp hjR
  have hkb := (le_div_iff₀ (by positivity : 0 < 2 * Real.logb 2 5)).mp hkR
  apply mem_literalTriangle_log_iff.mpr
  unfold triangleLogPoint
  nlinarith

theorem triangle_rectangle_lower_bound (a : ℕ) :
    triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a := by
  have h := (Finset.card_le_card (triangle_rectangle_subset a)).trans
    (triangle_card_le_actual_numerator a)
  have hc : ((Finset.range (triangleRectangleSide a 3)).product
      (Finset.range (triangleRectangleSide a 5))).card =
      triangleRectangleSide a 3 * triangleRectangleSide a 5 := by
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
  exact hc ▸ h

private theorem rectangleSide_dominates (a p : ℕ) (hp : 1 < p) :
    (a : ℝ) + 1 ≤ (2 * Real.logb 2 p + 1) * (triangleRectangleSide a p : ℝ) := by
  have hlog : 0 < Real.logb 2 (p : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hp)
  have hf := Nat.lt_floor_add_one ((a : ℝ) / (2 * Real.logb 2 p))
  have hs : (triangleRectangleSide a p : ℝ) =
      (⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ : ℝ) + 1 := by
    simp only [triangleRectangleSide, Nat.cast_add, Nat.cast_one]
  rw [← hs] at hf
  have hh := (div_lt_iff₀ (by positivity : 0 < 2 * Real.logb 2 p)).mp hf
  have h1 : (1 : ℝ) ≤ triangleRectangleSide a p := by
    rw [hs]
    have := Nat.cast_nonneg (α := ℝ) ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊
    linarith
  nlinarith



theorem triangleQuadraticDenominator_pos : 0 < triangleQuadraticDenominator := by
  have h3 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 5)
  unfold triangleQuadraticDenominator
  positivity
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution (a : ℕ) :
    (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2 := by
  constructor
  · apply (div_le_iff₀ triangleQuadraticDenominator_pos).mpr
    have h3 := rectangleSide_dominates a 3 (by decide)
    have h5 := rectangleSide_dominates a 5 (by decide)
    norm_num only [Nat.cast_ofNat] at h3 h5
    have hr : (triangleRectangleSide a 3 : ℝ) * triangleRectangleSide a 5 ≤
        dyadicOrderedBlockDigit235 a := by exact_mod_cast triangle_rectangle_lower_bound a
    have hprod := mul_le_mul h3 h5 (by positivity : (0 : ℝ) ≤ a + 1)
      (le_trans (by positivity : (0 : ℝ) ≤ a + 1) h3)
    calc
      (a + 1 : ℝ) ^ 2 ≤ triangleQuadraticDenominator *
          ((triangleRectangleSide a 3 : ℝ) * triangleRectangleSide a 5) := by
        unfold triangleQuadraticDenominator
        nlinarith only [hprod]
      _ ≤ (dyadicOrderedBlockDigit235 a : ℝ) * triangleQuadraticDenominator := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr triangleQuadraticDenominator_pos.le
  · exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a
