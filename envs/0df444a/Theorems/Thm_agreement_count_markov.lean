-- Prove2me | Theorems.Thm_agreement_count_markov
-- name    : agreement_count_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:49.897539+00:00
-- url     : https://prove2.me/theorems/1a781d46-5a3d-4c20-8d49-07ebae01d333
-- title:
--   agreement count markov: agreement count markov
-- statement:
--   Markov-type bound on the number of labelings with few disagreements.
--       For any h : α → Bool on a Fintype with |α| ≥ 1:
--       4 · #{f : #{x | f x ≠ h x} ≤ |α|/4} < 3 · 2^|α|.
--       This is the core of the double-averaging argument for NFL/PAC lower bounds.
--       Proof: Markov's inequality on agreements, using disagreement_sum_eq.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1076-L1133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1076-L1133

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

theorem agreement_count_markov {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) (hn : 1 ≤ Fintype.card α) :
    4 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4).card
    < 3 * 2 ^ Fintype.card α := by sorry
