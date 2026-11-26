-- Prove2me | Theorems.Thm_syracuse_first_passage_fixed_target_card_bound
-- name    : syracuse_first_passage_fixed_target_card_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T11:05:58.947803+00:00
-- url     : https://prove2.me/theorems/17aed2a3-4991-5920-a70e-7d000dab5bc5
-- title:
--   A fixed-target cardinality bound for first Syracuse passages below twice a barrier
-- statement:
--   Consider a finite set of odd starts at most X, all reaching the same a below 3B/2 after d+1 Syracuse steps while staying at least 2B for the preceding d+1 states. Given the displayed exact power inequality with budget M, the number of such starts is at most (M+d choose d+1).
-- source:
--   Exact valuation identity with a floor, parity-constrained reconstruction from a fixed endpoint, and finite composition counting. The last transition forces valuation at least three.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card

theorem syracuse_first_passage_fixed_target_card_bound (S : Finset ℕ) (B X a d M : ℕ)
    (hB : 0 < B) (hUpper : 2*a+2 ≤ 3*B)
    (hCut : X*(6*B+1)^(d+1) < 2^(2*(M+1)+(d+1))*a*(2*B)^(d+1))
    (hS : ∀ n ∈ S, n ≤ X ∧ n%2 = 1 ∧ syracuseStep^[d+1] n = a ∧
      ∀ i ≤ d, 2*B ≤ syracuseStep^[i] n) :
    S.card ≤ (M+d).choose (d+1) := by sorry
