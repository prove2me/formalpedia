-- Prove2me | Theorems.Thm_compress_injective_on_labelings
-- name    : compress_injective_on_labelings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:57.325302+00:00
-- url     : https://prove2.me/theorems/3dfaaa4d-1b81-47b7-ab5e-f02a7f517e19
-- title:
--   compress injective on labelings: compress injective on labelings
-- statement:
--   Pigeonhole core: compress is injective on C-realizable labelings.
--       If two C-realizable samples over the same points with different labelings
--       produce the same compressed set, correctness forces the labelings to agree.
--       Γ₇₃: now requires realizability hypotheses for both samples.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1794-L1816
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1794-L1816

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

theorem compress_injective_on_labelings {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionScheme X Bool C)
    (pts : Fin n → X) (_hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by sorry
