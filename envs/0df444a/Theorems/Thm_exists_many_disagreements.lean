-- Prove2me | Theorems.Thm_exists_many_disagreements
-- name    : exists_many_disagreements
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:39.491603+00:00
-- url     : https://prove2.me/theorems/8265ef53-9255-4ecd-a2c3-c637754cd53e
-- title:
--   exists many disagreements: exists many disagreements
-- statement:
--   Pigeonhole consequence: for any h on a Fintype with card ≥ 2,
--       there exists a function f disagreeing with h on more than |α|/4 points.
--       This is the per-sample NFL counting lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1014-L1069
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1014-L1069

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

theorem exists_many_disagreements {α : Type*} [Fintype α]
    (h : α → Bool) (hcard : 2 ≤ Fintype.card α) :
    ∃ f : α → Bool,
      Fintype.card α < 4 * (Finset.univ.filter fun x => f x ≠ h x).card := by sorry
