-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_11
-- name    : XinMartingaleInventory.Minimax.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:58:56.943058+00:00
-- url     : https://prove2.me/theorems/142bccc8-5af3-4d52-93ab-9cb585e7810d
-- title:
--   Lemma 11 — Explicit majorizing lines
-- statement:
--   Standing setting: positive rational U,b, integer T≥2. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 11. For each fixed x ∈ [0,U], 𝒦^T(x,d) ≥ f^T(x,d) for all d ∈ [0,U]. Also, for all ℓ ∈ [Υ^{T−1}_x,T−2], ℒ^T_ℓ(x,d) ≥ f^T(x,d) for all d ∈ [0,U].
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
--   - encoding: z is the infimum over nonnegative d where the threshold is defined → take the infimum within [0,U]; reason: d=U is feasible and no d>U can decrease the infimum; the source formulas are defined on [0,U]
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 11, p.23 (PDF p.23)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_11 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 2 ≤ T) (x : ℝ) (hx : x ∈ Set.Icc 0 (U : ℝ)) :
    (∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), nextObjective U b T x d ≤ majorantK U b T x d) ∧
    (∀ l : ℤ, upsilon U b (T-1) x ≤ l → l ≤ (T : ℤ)-2 →
      ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), nextObjective U b T x d ≤ majorantL U b T l x d) := by sorry

end XinMartingaleInventory.Minimax
