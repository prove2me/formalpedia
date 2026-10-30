-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_7
-- name    : XinMartingaleInventory.Minimax.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:58:46.266299+00:00
-- url     : https://prove2.me/theorems/d7c4a76e-9f1a-462e-a872-de07b54b32c2
-- title:
--   Lemma 7 — Continuation-value identity
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 7. For all T ≥ 1, x,d ∈ [0,U], ḡ^T(x,d) = g^T(max(β^T_d,x − d),d).
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
--   - encoding: z is the infimum over nonnegative d where the threshold is defined → take the infimum within [0,U]; reason: d=U is feasible and no d>U can decrease the infimum; the source formulas are defined on [0,U]
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 7, p.22 (PDF p.22)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_7 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (x d : ℝ) (hx : x ∈ Set.Icc 0 (U : ℝ))
    (hd : d ∈ Set.Icc 0 (U : ℝ)) :
    continuation U b T x d = explicitG U b T (max (beta U b T d : ℝ) (x-d)) d := by sorry

end XinMartingaleInventory.Minimax
