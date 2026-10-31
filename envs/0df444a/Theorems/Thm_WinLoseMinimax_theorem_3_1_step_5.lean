-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_3_1_step_5
-- name    : WinLoseMinimax.theorem_3_1_step_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:51.318858+00:00
-- url     : https://prove2.me/theorems/f6261286-a23e-4506-9eef-5d8cefc3b6cd
-- title:
--   Proof of Theorem 3.1, Step 5, pp.13–14 — a game violating the minimax property has a countable violating subgame
-- statement:
--   Let $G=(S,T,\pi)$ be a game (of any cardinality) that violates the minimax property. Then $G$ has a countable subgame $G'=(S',T',\pi')$, with $S'\subseteq S$ and $T'\subseteq T$ countably infinite, that violates the minimax property.
--
--   This reduces Theorem 3.1 for arbitrary games to the countable case.
--
--   **Formalization Note** "Countable" is Definition 1.1's $|S'|=|T'|=\aleph_0$: `Set.Countable` and `Set.Infinite` for both. The construction in the proof yields $S'$, $T'$ at most countable; a violating subgame cannot have a finite side, since a game with finitely many strategies for one player satisfies the minimax property.
--
--   Differences from the source:
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - reading: "a countable subgame" (the proof's construction gives S′, T′ "at most countable", p.14) → S′ and T′ countably infinite (`Set.Countable` and `Set.Infinite`); reason: Definition 1.1 defines a countable game by |S| = |T| = ℵ₀; the readings agree, since a subgame with a finite side satisfies the minimax property, so the stronger one is taken
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 3.1, Step 5, pp.13–14

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 3.1, Step 5: reduction to a countable subgame.** Holzman,
arXiv:2310.19314v1, proof of Theorem 3.1, Step 5, pp.13–14: let `G = (S, T, π)` be a game that
violates the minimax property. Then `G` has a countable subgame `G' = (S', T', π')` that violates
the minimax property.

**Formalization Note.** Any game: `S`, `T` arbitrary non-empty types of any cardinality.
"Countable" is Definition 1.1's `|S'| = |T'| = ℵ₀`: `Set.Countable` and `Set.Infinite` for both
`S'` and `T'` (so both are non-empty, as a subgame must be). The proof's construction gives `S'`,
`T'` at most countable (p.14); a violating subgame has no finite side, since a game in which one
player has finitely many pure strategies satisfies the minimax property. -/
theorem theorem_3_1_step_5 {S : Type u} {T : Type v} [Nonempty S] [Nonempty T]
    (π : S → T → Bool) (h : ¬ MinimaxProperty π) :
    ∃ (S' : Set S) (T' : Set T), S'.Countable ∧ S'.Infinite ∧ T'.Countable ∧ T'.Infinite ∧
      ¬ MinimaxProperty (restrict π S' T') := by sorry

end WinLoseMinimax
