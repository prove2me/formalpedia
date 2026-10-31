-- Prove2me | Theorems.Thm_WinLoseMinimax_corollary_2_12
-- name    : WinLoseMinimax.corollary_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:48.349091+00:00
-- url     : https://prove2.me/theorems/89bf02a2-40be-464d-9ad5-b5753ebfcc87
-- title:
--   Corollary 2.12, p.11 — finite columns and LNG-free: $\sup\min=1=\min\sup$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$, $T$ countably infinite) such that all sets in $\mathcal B^2(G)$ are finite, i.e. every column of the matrix of $G$ has finitely many 0's, and assume that $G$ is LNG-free. Then
--
--   $$\sup_{p\in\Delta(S)}\min_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)=1=\min_{q\in\Delta(T)}\sup_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q).$$
--
--   That is: the outer infimum over $q$ is attained, the inner infimum over $q$ is attained for every $p$, and both sides equal $1$.
--
--   This is the case used in Step 1 of the proof of Theorem 3.1. The countability of $S$ and $T$ is essential: for a $1\times1$ game with payoff 0 both sides equal 0.
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Corollary 2.12, p.11

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Corollary 2.12.** Holzman, arXiv:2310.19314v1, Corollary 2.12, p.11: let `G = (S, T, π)` be
a countable game such that all sets in the family `B²(G)` are finite, and assume that `G` is
LNG-free. Then
`sup_{p ∈ ∆(S)} min_{q ∈ ∆(T)} π_mix(p, q) = 1 = min_{q ∈ ∆(T)} sup_{p ∈ ∆(S)} π_mix(p, q)`.

**Formalization Note.** "All sets in `B²(G)` are finite" is `∀ t, (colSet π t).Finite`.
"Countable game" means countably infinite `S` and `T`; the corollary is false for a `1 × 1` game
with payoff `0`. The conclusion has four clauses: the outer `min` over `q` is attained, the inner
`min` over `q` is attained for every `p`, and both sides equal `1`. -/
theorem corollary_2_12 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool)
    (hfin : ∀ t, (colSet π t).Finite) (hfree : LNGFree π) :
    (∃ q₀ : PMF T, (⨆ p : PMF S, payoff π p q₀) = ⨅ q : PMF T, ⨆ p : PMF S, payoff π p q) ∧
      (∀ p : PMF S, ∃ q₀ : PMF T, payoff π p q₀ = ⨅ q : PMF T, payoff π p q) ∧
      (⨆ p : PMF S, ⨅ q : PMF T, payoff π p q) = 1 ∧
      (⨅ q : PMF T, ⨆ p : PMF S, payoff π p q) = 1 := by sorry

end WinLoseMinimax
