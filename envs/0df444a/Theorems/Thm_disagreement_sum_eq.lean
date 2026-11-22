-- Prove2me | Theorems.Thm_disagreement_sum_eq
-- name    : disagreement_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:54.363583+00:00
-- url     : https://prove2.me/theorems/ed239516-1e7a-43fc-a104-92030e9b09b4
-- title:
--   disagreement sum eq: disagreement sum eq
-- statement:
--   For any h : α → Bool on a Fintype, the sum over all functions f : α → Bool of
--       #{x | f x ≠ h x} equals |α| * 2^(|α| - 1).
--       This is the key counting identity for the NFL theorem:
--       each point x contributes 2^(|α|-1) to the sum (exactly half the functions
--       disagree with h at x).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L956-L1009
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L956-L1009

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
open Finset

theorem disagreement_sum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) :
    ∑ f : α → Bool,
      (univ.filter fun x => f x ≠ h x).card =
    Fintype.card α * 2 ^ (Fintype.card α - 1) := by sorry
