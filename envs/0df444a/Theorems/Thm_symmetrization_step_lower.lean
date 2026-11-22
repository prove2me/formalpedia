-- Prove2me | Theorems.Thm_symmetrization_step_lower
-- name    : symmetrization_step_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:42.799802+00:00
-- url     : https://prove2.me/theorems/328d5724-7e0c-46c4-985a-85c9b27ef0dd
-- title:
--   symmetrization step lower: symmetrization step lower
-- statement:
--   Symmetrization step for the lower tail:
--       P[∃h: EmpErr-TrueErr ≥ ε] ≤
--       2·P_{double}[∃h: EmpErr_S-EmpErr_{S'} ≥ ε/2].
--
--       Mirror of `symmetrization_step` for the opposite direction.
--       Uses `hoeffding_one_sided_upper` instead of `hoeffding_one_sided`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1164-L1271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1164-L1271

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem symmetrization_step_lower {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2} := by sorry
