-- Prove2me | Theorems.Thm_pac_lower_bound_good_event_le_half
-- name    : pac_lower_bound_good_event_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:40.350239+00:00
-- url     : https://prove2.me/theorems/3940f86b-12f6-4086-b0dd-ee7f18be242f
-- title:
--   pac lower bound good event le half: pac lower bound good event le half
-- statement:
--   The pac lower bound good event le half construction uses the pac lower bound good event le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1510-L1699
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1510-L1699

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

theorem pac_lower_bound_good_event_le_half
    (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    {T : Finset X} (hTne : T.Nonempty) (L : BatchLearner X Bool)
    (m : ℕ) (c₀ : X → Bool) (ε : ℝ) (hε1 : ε ≤ 1 / 4)
    (hcount : 2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        c₀ ((↑t : X)) ≠ L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
      ≤ T.card).card ≤ Fintype.card (Fin m → ↥T)) :
    ∃ D : MeasureTheory.Measure X, MeasureTheory.IsProbabilityMeasure D ∧
      MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε } ≤ ENNReal.ofReal (1 / 2 : ℝ) := by sorry
