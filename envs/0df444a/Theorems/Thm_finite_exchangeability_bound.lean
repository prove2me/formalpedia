-- Prove2me | Theorems.Thm_finite_exchangeability_bound
-- name    : finite_exchangeability_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:26.270623+00:00
-- url     : https://prove2.me/theorems/091b4643-386b-45c4-9cc1-ed0bf1522e37
-- title:
--   finite exchangeability bound: finite exchangeability bound
-- statement:
--   Generic finite exchangeability bound. Given a measure-preserving family of
--       transformations on a probability space, a NullMeasurableSet S, and a pointwise
--       bound on the sum of preimage indicators, conclude ν(S) ≤ B.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L666-L703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L666-L703

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

theorem finite_exchangeability_bound
    {Ω G : Type*} [MeasurableSpace Ω] [Fintype G] [Nonempty G]
    {ν : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ν]
    (T : G → Ω → Ω)
    (S : Set Ω)
    (hT : ∀ g, MeasureTheory.MeasurePreserving (T g) ν ν)
    (hS0 : MeasureTheory.NullMeasurableSet S ν)
    (B : ENNReal)
    (hpointwise :
      ∀ z, (∑ g : G,
        (((T g) ⁻¹' S).indicator (1 : Ω → ENNReal)) z)
          ≤ B * (Fintype.card G : ENNReal)) :
    ν S ≤ B := by sorry
