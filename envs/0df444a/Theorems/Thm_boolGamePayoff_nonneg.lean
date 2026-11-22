-- Prove2me | Theorems.Thm_boolGamePayoff_nonneg
-- name    : boolGamePayoff_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:57.460801+00:00
-- url     : https://prove2.me/theorems/1fa51c55-9332-41d4-9d2d-82466bcf41ca
-- title:
--   bool Game Payoff nonneg: bool Game Payoff nonneg
-- statement:
--   The bool Game Payoff nonneg construction uses the bool Game Payoff nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L94-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L94-L98

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem boolGamePayoff_nonneg {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    0 ≤ boolGamePayoff M p c := by sorry
