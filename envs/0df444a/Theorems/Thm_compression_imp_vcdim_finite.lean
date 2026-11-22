-- Prove2me | Theorems.Thm_compression_imp_vcdim_finite
-- name    : compression_imp_vcdim_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:58.203814+00:00
-- url     : https://prove2.me/theorems/97b71c5b-d2ed-4ee1-9d49-7c813e2f9a28
-- title:
--   compression imp vcdim finite: compression imp vcdim finite
-- statement:
--   ∃ compression scheme → VCDim < ⊤.
--       Pigeonhole: compress is injective on C-realizable labelings (by correctness),
--       but compressed subsets of an n-point sample are bounded. Shatters X C T
--       guarantees ALL labelings are C-realizable, so injectivity holds on all 2^n
--       labelings. Contradiction for large n.
--       Γ₇₃ RESOLVED: CompressionScheme parameterized by C with realizability guard.
--       Shattered sets guarantee C-realizability of every labeling, so the
--       pigeonhole argument is genuinely non-vacuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1886-L2001
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1886-L2001

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

theorem compression_imp_vcdim_finite (X : Type u)
    (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by sorry
