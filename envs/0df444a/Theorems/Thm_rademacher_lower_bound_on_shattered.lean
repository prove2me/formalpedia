-- Prove2me | Theorems.Thm_rademacher_lower_bound_on_shattered
-- name    : rademacher_lower_bound_on_shattered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:09.562967+00:00
-- url     : https://prove2.me/theorems/4d77ad9a-b260-4548-847e-b81cb08582aa
-- title:
--   rademacher lower bound on shattered: rademacher lower bound on shattered
-- statement:
--   Adversarial Rademacher lower bound on shattered sets.
--       For |T| >= 4m^2 + 1, exists D with Rad_m(C,D) >= 1 / 2.
--
--       Proof: D = uniform on T. Product measure = uniform on T^m.
--       On injective samples from T (shattered): EmpRad = 1
--       (by empRad_eq_one_of_injective_in_shattered).
--       EmpRad ≥ 0 everywhere (by empRad_nonneg).
--       Birthday bound: P[injective m draws from n ≥ 4m²+1 points] ≥ 1 - m(m-1)/(2n) ≥ 7 / 8 ≥ 1 / 2.
--       So ∫ EmpRad ≥ P[injective] · 1 + P[¬injective] · 0 ≥ 1 / 2.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L1270-L1434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L1270-L1434

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem rademacher_lower_bound_on_shattered (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (T : Finset X) (hT : Shatters X C T)
    (m : ℕ) (hm : 0 < m) (hT_large : 4 * m ^ 2 + 1 ≤ T.card) :
    ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      (1 : ℝ) / 2 ≤ RademacherComplexity X C D m := by sorry
