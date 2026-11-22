-- Prove2me | Theorems.Thm_block_extract_disjoint
-- name    : block_extract_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:12.693484+00:00
-- url     : https://prove2.me/theorems/a03be49a-d6d9-4329-9172-0a0479d0d951
-- title:
--   block extract disjoint: block extract disjoint
-- statement:
--   Block index sets are disjoint for distinct blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L35-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L35-L40

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem block_extract_disjoint (k m : ℕ) (j₁ j₂ : Fin k) (hne : j₁ ≠ j₂) :
    Disjoint
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₁, i)) Finset.univ)
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₂, i)) Finset.univ) := by sorry
