-- Prove2me | Theorems.Thm_shatters_hard_labeling
-- name    : shatters_hard_labeling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:19.201434+00:00
-- url     : https://prove2.me/theorems/5e6db2a4-f234-4546-88ec-583f67963edd
-- title:
--   shatters hard labeling: shatters hard labeling
-- statement:
--   Key counting lemma: for any h : ↥T → Bool on a shattered set T with |T| ≥ 2,
--       there exists c ∈ C with #{x ∈ T | c x ≠ h x} > |T|/4.
--       Lifts exists_many_disagreements through shattering.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L124-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L124-L133

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

theorem shatters_hard_labeling {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (h : ↥T → Bool) (hcard : 2 ≤ T.card) :
    ∃ c ∈ C, T.card <
      4 * (Finset.univ.filter fun x : ↥T => c (x : X) ≠ h x).card := by sorry
