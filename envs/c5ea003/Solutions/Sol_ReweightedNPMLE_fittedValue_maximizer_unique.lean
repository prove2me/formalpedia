-- Prove2me | solution 1 for ReweightedNPMLE.fittedValue_maximizer_unique
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:13:45.750235+00:00
-- url     : https://prove2.me/submissions/92cdda3c-8266-4459-9ce5-8e8092782663

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_strictConcaveOn_weightedLogLikelihood

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Strict concavity makes the fitted-value maximizer unique on any convex feasible set. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {u v : Fin n → ℝ}
    (hu : IsMaxOn C (weightedLogLikelihood w) u)
    (hv : IsMaxOn C (weightedLogLikelihood w) v) : u = v := by
  by_contra huv
  let m := (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v
  have hm : m ∈ C := hC hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
  have hstrict := ((strictConcaveOn_weightedLogLikelihood hw).subset hCpos hC).2
    hu.1 hv.1 huv (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)
  have huv_obj : weightedLogLikelihood w u = weightedLogLikelihood w v :=
    le_antisymm (hv.2 u hu.1) (hu.2 v hv.1)
  have hm_le : weightedLogLikelihood w m ≤ weightedLogLikelihood w u := hu.2 m hm
  change (2 : ℝ)⁻¹ • weightedLogLikelihood w u +
      (2 : ℝ)⁻¹ • weightedLogLikelihood w v < weightedLogLikelihood w m at hstrict
  rw [← huv_obj] at hstrict
  have hstrict' : weightedLogLikelihood w u < weightedLogLikelihood w m := by
    calc
      weightedLogLikelihood w u = (2 : ℝ)⁻¹ • weightedLogLikelihood w u +
          (2 : ℝ)⁻¹ • weightedLogLikelihood w u := by
            norm_num [smul_eq_mul]
            ring
      _ < weightedLogLikelihood w m := hstrict
  exact (not_lt_of_ge hm_le) hstrict'
