-- Prove2me | solution 1 for ReweightedNPMLE.likelihoodContactNumerator_le_total_of_isMaxOn
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:53:17.399973+00:00
-- url     : https://prove2.me/submissions/44ad2b8d-8bf5-4b24-949a-e95a01a11174

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Directional optimality of a positive weighted fitted-value maximizer. -/
theorem solution
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactNumerator w v a ≤ total w := by
  let g : ℝ → ℝ := fun t ↦
    weightedLogLikelihood w (v + t • (a - v))
  have hvpos : ∀ i, 0 < v i := hCpos hvmax.1
  have hderiv : HasDerivAt g
      (∑ i : Fin n, w i * ((a i - v i) / v i)) 0 := by
    have hi (i : Fin n) : HasDerivAt
        (fun t : ℝ ↦ w i * Real.log (v i + t * (a i - v i)))
        (w i * ((a i - v i) / v i)) 0 := by
      have hlin : HasDerivAt (fun t : ℝ ↦ v i + t * (a i - v i))
          (a i - v i) 0 := by
        exact (hasDerivAt_mul_const (x := (0 : ℝ)) (a i - v i)).const_add (v i)
      have hne : v i + (0 : ℝ) * (a i - v i) ≠ 0 := by
        simpa using (hvpos i).ne'
      simpa using (hlin.log hne).const_mul (w i)
    simpa [g, weightedLogLikelihood] using
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hi i)
  have hgmax : IsLocalMaxOn g (Icc (0 : ℝ) 1) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htC : v + t • (a - v) ∈ C := by
      have hrepr : v + t • (a - v) = (1 - t) • v + t • a := by module
      rw [hrepr]
      exact hC hvmax.1 ha (sub_nonneg.mpr ht.2) ht.1 (by ring)
    simpa [g] using hvmax.2 _ htC
  have hone_tangent : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa using (segment_subset_Icc (𝕜 := ℝ) (show (0 : ℝ) ≤ 1 by norm_num))
  have hnonpos := hgmax.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hone_tangent
  have hdirection : (∑ i : Fin n, w i * ((a i - v i) / v i)) ≤ 0 := by
    simpa using hnonpos
  have hdiff :
    (∑ i : Fin n, w i * (a i / v i)) - ∑ i, w i =
        ∑ i, w i * ((a i - v i) / v i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hvpos i).ne']
  unfold likelihoodContactNumerator total
  linarith
