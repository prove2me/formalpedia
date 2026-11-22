-- Prove2me | Theorems.Thm_compress_with_info_injective_on_labelings
-- name    : compress_with_info_injective_on_labelings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:06.772404+00:00
-- url     : https://prove2.me/theorems/9be5397e-7398-4034-ab84-79ef417de074
-- title:
--   compress with info injective on labelings: compress with info injective on labelings
-- statement:
--   Pigeonhole core: if two C-realizable samples over the same points with
--       different labelings produce the same (kernel, info) pair, correctness
--       forces the labelings to agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1099-L1121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1099-L1121

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable

theorem compress_with_info_injective_on_labelings {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionSchemeWithInfo X Bool C)
    (pts : Fin n → X) (_hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by sorry
