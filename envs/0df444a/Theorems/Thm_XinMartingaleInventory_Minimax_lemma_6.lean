-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_6
-- name    : XinMartingaleInventory.Minimax.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:13.900001+00:00
-- url     : https://prove2.me/theorems/4ee036ff-c410-43ae-9826-d98062d3137b
-- title:
--   Lemma 6 — Explicit minimizing threshold
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 6. β^T_d ∈ arg min_{z∈[0,U]} g^T(z,d).
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 6, p.21 (PDF p.21)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_6 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (d : ℝ) (hd : d ∈ Set.Icc 0 (U : ℝ)) :
    (beta U b T d : ℝ) ∈ Set.Icc 0 (U : ℝ) ∧
    ∀ z ∈ Set.Icc (0 : ℝ) (U : ℝ),
      explicitG U b T (beta U b T d) d ≤ explicitG U b T z d := by sorry

end XinMartingaleInventory.Minimax
