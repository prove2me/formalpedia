-- Prove2me | Theorems.Thm_boolGamePayoff_eq_boolTestExpectation
-- name    : boolGamePayoff_eq_boolTestExpectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:33.744365+00:00
-- url     : https://prove2.me/theorems/be3f6764-9d98-4638-b6c4-7830579a1ec6
-- title:
--   bool Game Payoff eq bool Test Expectation: bool Game Payoff eq bool Test Expectation
-- statement:
--   Identifies the game-theoretic payoff (a row distribution against a fixed column in
--   the Bool game) with the corresponding test expectation. The translation that lets the
--   MWU regret bound be applied directly to the compression problem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L173-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L173-L177

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem boolGamePayoff_eq_boolTestExpectation
    {R : Type*} [Fintype R]
    {C : Type*} (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    boolGamePayoff M p c = boolTestExpectation p (fun r => M r c) := by sorry
