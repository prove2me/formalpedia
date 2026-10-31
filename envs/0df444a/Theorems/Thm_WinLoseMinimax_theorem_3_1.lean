-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_3_1
-- name    : WinLoseMinimax.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:58.11126+00:00
-- url     : https://prove2.me/theorems/56da4a51-88b8-4728-bfac-86e0adda33ad
-- title:
--   Theorem 3.1, p.11 — a game is totally minimax if and only if it is LNG-free
-- statement:
--   Let $G=(S,T,\pi)$ be a two-person win-lose game: $S$ and $T$ are arbitrary non-empty sets of pure strategies (of any cardinality) and $\pi:S\times T\to\{0,1\}$. Mixed strategies are probability distributions with at most countable support, and $\pi_{\mathrm{mix}}(p,q)$ is the probability that player 1 wins. Then
--
--   $$G\ \text{is totally minimax}\iff G\ \text{is LNG-free}.$$
--
--   Here **totally minimax** means that every subgame $(S',T',\pi|_{S'\times T'})$ with non-empty $S'\subseteq S$, $T'\subseteq T$ satisfies
--
--   $$\sup_{p\in\Delta(S')}\inf_{q\in\Delta(T')}\pi_{\mathrm{mix}}(p,q)=\inf_{q\in\Delta(T')}\sup_{p\in\Delta(S')}\pi_{\mathrm{mix}}(p,q),$$
--
--   and **LNG-free** means that no subgame is isomorphic to the larger number game, in which both players pick a positive integer and player 1 wins iff $s\ge t$.
--
--   The presence of a copy of LNG is the only obstruction to being totally minimax. The theorem removes the finite VC-dimension hypothesis of Hanneke, Livni and Moran.
--
--   **Formalization Note** $S$ and $T$ live in arbitrary universes. $\Delta(X)$ is `PMF X`, with values in `ℝ≥0∞`. Non-emptiness of the subgames is explicit, as Definition 1.1 requires of every game.
--
--   Differences from the source:
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
--   - encoding: subgames are games, hence have non-empty strategy sets (Definitions 1.1, 1.4) → `S'.Nonempty` and `T'.Nonempty` explicit in `TotallyMinimax`; reason: the paper's definition; stated explicitly because an empty subgame would read 0 = ⊤
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Theorem 3.1, p.11

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Theorem 3.1 (characterization of totally minimax games).** Holzman, arXiv:2310.19314v1,
Theorem 3.1, p.11: let `G = (S, T, π)` be a game. Then `G` is totally minimax if and only if `G`
is LNG-free.

**Formalization Note.** Every game: `S`, `T` arbitrary non-empty types in arbitrary universes, of
any cardinality, and `π : S → T → Bool` arbitrary. Mixed strategies are `PMF` (countable support,
p.3); payoffs and sup/inf in `ℝ≥0∞`. Totally minimax ranges over all pairs of non-empty subsets
`S' ⊆ S`, `T' ⊆ T` (`TotallyMinimax`); LNG-free is the absence of a subgame isomorphic to the
larger number game (`LNGFree`). -/
theorem theorem_3_1 {S : Type u} {T : Type v} [Nonempty S] [Nonempty T]
    (π : S → T → Bool) :
    TotallyMinimax π ↔ LNGFree π := by sorry

end WinLoseMinimax
