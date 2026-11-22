-- Prove2me | Theorems.Thm_zeroOneLoss_faithful
-- name    : zeroOneLoss_faithful
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:36.31603+00:00
-- url     : https://prove2.me/theorems/5225b465-26e6-4633-83f0-b10837b0fadb
-- title:
--   zero One Loss faithful: zero One Loss faithful
-- statement:
--   The 0-1 loss is faithful.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L321-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L321-L324

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

theorem zeroOneLoss_faithful : IsFaithfulLoss (zeroOneLoss Bool) := by sorry
