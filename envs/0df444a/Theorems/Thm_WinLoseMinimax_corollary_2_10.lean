-- Prove2me | Theorems.Thm_WinLoseMinimax_corollary_2_10
-- name    : WinLoseMinimax.corollary_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:44.778637+00:00
-- url     : https://prove2.me/theorems/f4249e32-f242-47e6-a26a-3eb4ec7637d4
-- title:
--   Corollary 2.10, p.10 — finite rows and LNG-free: $\max\inf=0=\inf\max$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$, $T$ countably infinite) such that all sets in $\mathcal B^1(G)$ are finite, and assume that $G$ is LNG-free (equivalently, by Proposition 2.9, $\mathcal B^1_{\mathrm{down}}(G)$ is ascending-union closed, or contains no countable ascending chain). Then
--
--   $$\max_{p\in\Delta(S)}\inf_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)=0=\inf_{q\in\Delta(T)}\max_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q).$$
--
--   That is: the outer supremum over $p$ is attained, the inner supremum over $p$ is attained for every $q$, and both sides equal $0$.
--
--   The countability of $S$ and $T$ is essential: for a $1\times1$ game with payoff 1 both sides equal 1.
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: "G satisfies one (hence all) of the equivalent conditions (1)–(3) in Proposition 2.9" → hypothesis: condition (3), `LNGFree π`; reason: the three conditions are equivalent under the corollary's finite-row hypothesis (Proposition 2.9)
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Corollary 2.10, p.10

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Corollary 2.10.** Holzman, arXiv:2310.19314v1, Corollary 2.10, p.10: let `G = (S, T, π)` be
a countable game such that all sets in the family `B¹(G)` are finite, and assume that `G`
satisfies one (hence all) of the equivalent conditions (1)–(3) of Proposition 2.9. Then
`max_{p ∈ ∆(S)} inf_{q ∈ ∆(T)} π_mix(p, q) = 0 = inf_{q ∈ ∆(T)} max_{p ∈ ∆(S)} π_mix(p, q)`.

**Formalization Note.** The hypothesis is condition (3), LNG-freeness (equivalent to (1) and (2)
by Proposition 2.9). "Countable game" means countably infinite `S` and `T`; the corollary is false
for a `1 × 1` game with payoff `1`. The conclusion has four clauses: the outer `max` over `p` is
attained, the inner `max` over `p` is attained for every `q`, and both sides equal `0`. -/
theorem corollary_2_10 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool)
    (hfin : ∀ s, (rowSet π s).Finite) (hfree : LNGFree π) :
    (∃ p₀ : PMF S, (⨅ q : PMF T, payoff π p₀ q) = ⨆ p : PMF S, ⨅ q : PMF T, payoff π p q) ∧
      (∀ q : PMF T, ∃ p₀ : PMF S, payoff π p₀ q = ⨆ p : PMF S, payoff π p q) ∧
      (⨆ p : PMF S, ⨅ q : PMF T, payoff π p q) = 0 ∧
      (⨅ q : PMF T, ⨆ p : PMF S, payoff π p q) = 0 := by sorry

end WinLoseMinimax
