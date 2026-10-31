-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_2_11
-- name    : WinLoseMinimax.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:11.263998+00:00
-- url     : https://prove2.me/theorems/962338ea-b816-4f7d-9d66-760f66592001
-- title:
--   Theorem 2.11, p.11 — ascending-union closed $B^2_{down}(G)$ gives $\sup\min=\min\sup$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$, $T$ countably infinite) such that the family $\mathcal B^2_{\mathrm{down}}(G)$ is ascending-union closed. Then $G$ satisfies the minimax property in the form
--
--   $$\sup_{p\in\Delta(S)}\min_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)=\min_{q\in\Delta(T)}\sup_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q).$$
--
--   That is:
--
--   1. the outer infimum over $q$ is attained;
--   2. for every $p\in\Delta(S)$ the inner infimum over $q$ is attained;
--   3. the two sides are equal.
--
--   This is the dual of Theorem 2.2 with the roles of the players interchanged. It yields Corollary 2.12.
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: A₁ ⊂ A₂ ⊂ ⋯ in Definition 2.1 (strictness not printed), i = 1, 2, … → `AscendingUnionClosed`: chains `A : ℕ → Set α` with `StrictMono A`; reason: a non-strict chain is eventually constant, so its union is a member, or has a strictly increasing subsequence with the same union; the two readings define the same families
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Theorem 2.11, p.11

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Theorem 2.11 (dual of Theorem 2.2).** Holzman, arXiv:2310.19314v1, Theorem 2.11, p.11: let
`G = (S, T, π)` be a countable game such that the family `B²_down(G)` is ascending-union closed.
Then `G` satisfies the minimax property in the form
`sup_{p ∈ ∆(S)} min_{q ∈ ∆(T)} π_mix(p, q) = min_{q ∈ ∆(T)} sup_{p ∈ ∆(S)} π_mix(p, q)`.

**Formalization Note.** The three clauses are: the outer `min` over `q` is attained; for every
`p` the inner `min` over `q` is attained; and the equality. "Countable game" is
`[Countable S] [Infinite S] [Countable T] [Infinite T]`. -/
theorem theorem_2_11 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool)
    (hAUC : AscendingUnionClosed (B2down π)) :
    (∃ q₀ : PMF T, (⨆ p : PMF S, payoff π p q₀) = ⨅ q : PMF T, ⨆ p : PMF S, payoff π p q) ∧
      (∀ p : PMF S, ∃ q₀ : PMF T, payoff π p q₀ = ⨅ q : PMF T, payoff π p q) ∧
      MinimaxProperty π := by sorry

end WinLoseMinimax
