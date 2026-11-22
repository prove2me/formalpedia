-- Prove2me | Theorems.Thm_restriction_pattern_count
-- name    : restriction_pattern_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:25.168162+00:00
-- url     : https://prove2.me/theorems/e0af6c0e-4132-4798-b0fb-99e29c6ec286
-- title:
--   restriction pattern count: restriction pattern count
-- statement:
--   The number of distinct restriction patterns of C on any n points is at most GF(C,n).
--       For z : Fin n → X, define patterns(z) as the set of `p : Fin n → Bool`
--       realized by some `h ∈ C` through `p i = (h (z i) ≠ c (z i))`.
--       Then patterns(z).ncard ≤ GrowthFunction X C n by definition of GrowthFunction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L550-L599
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L550-L599

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

theorem restriction_pattern_count {X : Type u} [Infinite X]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (n : ℕ) (z : Fin n → X) :
    Set.ncard {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} ≤
      GrowthFunction X C n := by sorry
