-- Prove2me | Theorems.Thm_pac_lower_bound_core
-- name    : pac_lower_bound_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:56.68188+00:00
-- url     : https://prove2.me/theorems/6860873b-1ac9-48f2-96be-ba7934547272
-- title:
--   pac lower bound core: pac lower bound core
-- statement:
--   PAC lower bound core: sample complexity is at least (d-1)/2.
--       For any PAC learner with VCDim = d, at least ⌈(d-1)/2⌉ samples needed.
--       Proof: construct d shattered points, uniform distribution, counting argument.
--       Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1704-L1784
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1704-L1784

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem pac_lower_bound_core (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : VCDim X C = d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    -- Any PAC learner needs at least ⌈(d-1)/(64ε)⌉ samples
    ∀ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
      (∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C, let m := mf ε δ
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)) →
      Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε (1 / 7) := by sorry
