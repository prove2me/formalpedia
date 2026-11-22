-- Prove2me | Theorems.Thm_empiricalError_bounded_diff
-- name    : empiricalError_bounded_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:43.226018+00:00
-- url     : https://prove2.me/theorems/43e0a990-3a1a-4ad4-9375-69e196ff1b02
-- title:
--   empirical Error bounded diff: empirical Error bounded diff
-- statement:
--   EmpiricalError of a fixed hypothesis h is a bounded-difference function
--       of the sample, with constant 1/m. Changing one sample point changes the
--       average loss by at most 1/m (since each term is in [0,1] for zeroOneLoss).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L448-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L448-L479

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

theorem empiricalError_bounded_diff {X : Type u}
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m) :
    HasBoundedDifferences
      (fun xs : Fin m → X =>
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool))
      (1 / m : ℝ) := by sorry
