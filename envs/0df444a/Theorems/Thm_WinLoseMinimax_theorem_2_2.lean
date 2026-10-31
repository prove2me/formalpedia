-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_2_2
-- name    : WinLoseMinimax.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:36.377986+00:00
-- url     : https://prove2.me/theorems/10b7136a-d5bc-4430-a8ff-7d89f2b4955a
-- title:
--   Theorem 2.2, p.6 — ascending-union closed $B^1_{down}(G)$ gives $\max\inf=\inf\max$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$, $T$ countably infinite) such that the family $\mathcal B^1_{\mathrm{down}}(G)$ is ascending-union closed. Then $G$ satisfies the minimax property in the form
--
--   $$\max_{p\in\Delta(S)}\inf_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)=\inf_{q\in\Delta(T)}\max_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q).\tag{3}$$
--
--   That is:
--
--   1. the outer supremum over $p$ is attained;
--   2. for every $q\in\Delta(T)$ the inner supremum over $p$ is attained;
--   3. the two sides are equal.
--
--   This is the paper's first main result, a combinatorial sufficient condition for the minimax property of a countable game. Through Corollaries 2.10 and 2.12 it feeds the proof of Theorem 3.1. The infimum over $q$ cannot in general be replaced by a minimum (Remark 2.5).
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: A₁ ⊂ A₂ ⊂ ⋯ in Definition 2.1 (strictness not printed), i = 1, 2, … → `AscendingUnionClosed`: chains `A : ℕ → Set α` with `StrictMono A`; reason: a non-strict chain is eventually constant, so its union is a member, or has a strictly increasing subsequence with the same union; the two readings define the same families
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Theorem 2.2, equation (3), p.6

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Theorem 2.2.** Holzman, arXiv:2310.19314v1, Theorem 2.2, p.6: let `G = (S, T, π)` be a
countable game such that the family `B¹_down(G)` is ascending-union closed. Then `G` satisfies the
minimax property in the form
`max_{p ∈ ∆(S)} inf_{q ∈ ∆(T)} π_mix(p, q) = inf_{q ∈ ∆(T)} max_{p ∈ ∆(S)} π_mix(p, q)`  (3).

**Formalization Note.** The three clauses are: the outer `max` over `p` is attained; for every `q`
the inner `max` over `p` is attained; and the equality (3). "Countable game" is
`[Countable S] [Infinite S] [Countable T] [Infinite T]`; mixed strategies are `PMF`; values in
`ℝ≥0∞`. -/
theorem theorem_2_2 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool)
    (hAUC : AscendingUnionClosed (B1down π)) :
    (∃ p₀ : PMF S, (⨅ q : PMF T, payoff π p₀ q) = ⨆ p : PMF S, ⨅ q : PMF T, payoff π p q) ∧
      (∀ q : PMF T, ∃ p₀ : PMF S, payoff π p₀ q = ⨆ p : PMF S, payoff π p q) ∧
      MinimaxProperty π := by sorry

end WinLoseMinimax
