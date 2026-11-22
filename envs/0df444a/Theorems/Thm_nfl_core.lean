-- Prove2me | Theorems.Thm_nfl_core
-- name    : nfl_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:41.1748+00:00
-- url     : https://prove2.me/theorems/479c158e-4835-454c-8772-391dc1169024
-- title:
--   nfl core: nfl core
-- statement:
--   NFL core: for any learner and any finite domain, there exists a hard
--       distribution and concept. Factors through uniformMeasure construction.
--       This is the core argument used by both nfl_fixed_sample and pac_lower_bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1387-L1508
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1387-L1508

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

theorem nfl_core (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    -- There exists a hard distribution and concept
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        -- The learner fails with positive probability
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 := by sorry
