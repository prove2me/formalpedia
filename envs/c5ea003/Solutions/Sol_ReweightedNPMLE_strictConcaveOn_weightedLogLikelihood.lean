-- Prove2me | solution 1 for ReweightedNPMLE.strictConcaveOn_weightedLogLikelihood
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:13:03.9757+00:00
-- url     : https://prove2.me/submissions/7b45251a-706e-4c5f-ba8e-0774c95e931a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- For positive weights, the finite log-likelihood is strictly concave in fitted values. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) :
    StrictConcaveOn ℝ (positiveVectors n) (weightedLogLikelihood w) := by
  classical
  refine ⟨convex_positiveVectors n, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hdiff : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    simpa using not_ne_iff.mp (not_exists.mp h i)
  have hcoord_le : ∀ i, a * Real.log (x i) + b * Real.log (y i) ≤
      Real.log (a * x i + b * y i) := by
    intro i
    simpa [smul_eq_mul] using
      strictConcaveOn_log_Ioi.concaveOn.2 (hx i) (hy i) ha.le hb.le hab
  have hcoord_lt : ∃ i, a * Real.log (x i) + b * Real.log (y i) <
      Real.log (a * x i + b * y i) := by
    obtain ⟨i, hi⟩ := hdiff
    refine ⟨i, ?_⟩
    simpa [smul_eq_mul] using
      strictConcaveOn_log_Ioi.2 (hx i) (hy i) hi ha hb hab
  calc
    a • weightedLogLikelihood w x + b • weightedLogLikelihood w y =
        ∑ i, w i * (a * Real.log (x i) + b * Real.log (y i)) := by
          simp only [weightedLogLikelihood, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ < ∑ i, w i * Real.log (a * x i + b * y i) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_le_mul_of_nonneg_left (hcoord_le i) (hw i).le
      · obtain ⟨i, hi⟩ := hcoord_lt
        exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hw i)⟩
    _ = weightedLogLikelihood w (a • x + b • y) := by
      simp [weightedLogLikelihood, smul_eq_mul]
