-- Prove2me | Theorems.Thm_WinLoseMinimax_example_1_3
-- name    : WinLoseMinimax.example_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:54.989293+00:00
-- url     : https://prove2.me/theorems/c5687a5a-138d-4698-b50c-2fa13c33485d
-- title:
--   Example 1.3, pp.3–4 — the larger number game: $\sup\inf=0$ and $\inf\sup=1$
-- statement:
--   In the **larger number game** each player chooses a positive integer and the larger number wins, ties going to player 1: $G=(\mathbb N,\mathbb N,\pi)$ with $\pi(s,t)=1$ if $s\ge t$ and $0$ otherwise. Mixed strategies are probability distributions $p,q$ on the positive integers. Then
--
--   $$\sup_{p\in\Delta(\mathbb N)}\inf_{q\in\Delta(\mathbb N)}\pi_{\mathrm{mix}}(p,q)=0,\qquad \inf_{q\in\Delta(\mathbb N)}\sup_{p\in\Delta(\mathbb N)}\pi_{\mathrm{mix}}(p,q)=1 .$$
--
--   So LNG violates the minimax property with the largest possible gap. This gives the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** Mixed strategies are `PMF ℕ`; values are in `ℝ≥0∞`.
--
--   Differences from the source:
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Example 1.3, pp.3–4

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

open scoped ENNReal

namespace WinLoseMinimax

/-- **Example 1.3: the larger number game violates the minimax property.** Holzman,
arXiv:2310.19314v1, Example 1.3, pp.3–4: for the larger number game `(ℕ, ℕ, π)` with
`π(s, t) = 1` iff `s ≥ t`, the left-hand side of equation (2) equals `0` and the right-hand side
equals `1`.

**Formalization Note.** Mixed strategies are `PMF ℕ` (= `∆(ℕ)`); payoffs and the sup/inf are in
`ℝ≥0∞`. The paper's positive integers are indexed from `0` (an isomorphism of games). -/
theorem example_1_3 :
    (⨆ p : PMF ℕ, ⨅ q : PMF ℕ, payoff lng p q) = 0 ∧
      (⨅ q : PMF ℕ, ⨆ p : PMF ℕ, payoff lng p q) = 1 := by sorry

end WinLoseMinimax
