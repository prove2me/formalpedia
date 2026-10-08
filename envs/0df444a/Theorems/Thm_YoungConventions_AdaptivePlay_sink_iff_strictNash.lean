-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_sink_iff_strictNash
-- name    : YoungConventions.AdaptivePlay.sink_iff_strictNash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:29.30435+00:00
-- url     : https://prove2.me/theorems/dff9733a-690f-4868-8d40-316ba0007c9b
-- title:
--   §4, p. 64 — sinks of the best-reply graph are the strict Nash equilibria; path form of weak acyclicity
-- statement:
--   Let $\Gamma$ be a game with finitely many players and finite nonempty strategy sets.
--   1. A strategy tuple $s$ is a sink of the best-reply graph if and only if $s$ is a strict pure Nash equilibrium.
--   2. $\Gamma$ is weakly acyclic if and only if from every strategy tuple $s$ there is a directed best-reply path, possibly of length zero, ending in a strict pure Nash equilibrium.
--
--   The second statement is the form of weak acyclicity that the proof of Theorem 1 uses: one player at a time switches to a best reply until a strict equilibrium is reached.
--
--   **Formalization Note** The page asserts only that every sink is a strict Nash equilibrium. The converse (a strict equilibrium has no outgoing edge) is immediate, and the paper's "if, and only if" uses it, so both directions are stated.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.AdaptivePlay

/-- **Sinks of the best-reply graph are the strict pure Nash equilibria; the path form of weak
acyclicity** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 64,
PDF p. 9): "Every sink of the best reply graph is clearly a strict Nash equilibrium in pure
strategies. So a game is weakly acyclic if, and only if, from every strategy-tuple there exists a
finite sequence of best replies by one agent at a time that ends in a strict, pure strategy Nash
equilibrium."

For a game with finite nonempty strategy sets:
1. a strategy tuple `s` is a sink of the best-reply graph if and only if it is a strict pure Nash
   equilibrium;
2. the game is weakly acyclic if and only if from every `s` a directed best-reply path leads to a
   strict pure Nash equilibrium.

**Formalization Note.** The page states only "sink ⇒ strict Nash equilibrium"; the converse
(a strict equilibrium has no exiting best-reply edge) is immediate and is what the "if, and only
if" of the next sentence uses, so both directions are stated. Paths are `Relation.ReflTransGen` of
the edge relation (length zero allowed). -/
theorem sink_iff_strictNash {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (u : ι → (∀ i, S i) → ℝ) :
    (∀ s : ∀ i, S i, IsSink u s ↔ IsStrictNash u s) ∧
      (WeaklyAcyclic u ↔ ∀ s : ∀ i, S i, ∃ s' : ∀ i, S i,
        Relation.ReflTransGen (BestReplyEdge u) s s' ∧ IsStrictNash u s') := by sorry

end YoungConventions.AdaptivePlay
