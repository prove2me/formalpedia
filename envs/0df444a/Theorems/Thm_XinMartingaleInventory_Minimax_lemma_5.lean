-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_5
-- name    : XinMartingaleInventory.Minimax.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:12.335994+00:00
-- url     : https://prove2.me/theorems/add1c140-2d02-4c46-9cf3-39b000b6a996
-- title:
--   Lemma 5 — Interlacing thresholds
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 5. A^T_j < A^{T+1}_{j+1} < A^T_{j+1} for j ∈ [0,T−2]. It follows that for all T ≥ 2 and d ∈ [0,U], Γ^T_d ∈ {Γ^{T−1}_d,Γ^{T−1}_d + 1}.
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 5, p.21 (PDF p.21)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_5 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) :
    (∀ j : ℤ, 0 ≤ j → j ≤ (T : ℤ)-2 →
      A U b T j < A U b (T+1) (j+1) ∧ A U b (T+1) (j+1) < A U b T (j+1)) ∧
    (2 ≤ T → ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ),
      gamma U b T d = gamma U b (T-1) d ∨ gamma U b T d = gamma U b (T-1) d + 1) := by sorry

end XinMartingaleInventory.Minimax
