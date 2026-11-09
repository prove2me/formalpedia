-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_strict_lex_descent
-- name    : XorParallelRepetition.Exponential.strict_lex_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:27.590475+00:00
-- url     : https://prove2.me/theorems/e3c58ff4-4eef-4466-816e-1def14945d42
-- title:
--   Lemma 3.3 — strict lexicographic descent
-- statement:
--   Let $\Psi$ be a generalized XOR game with at least one player that has an ordered contradiction of length $N$. Then there is a non-empty set $I$ of players such that $\Psi_{\mathrm{glue}(I)}$ has an ordered contradiction of the same length $N$ and
--
--   $$
--   H_N(\Psi_{\mathrm{glue}(I)})<H_N(\Psi)
--   $$
--
--   in the lexicographic order.
--
--   This descent drives the iteration of Lemma 3.4.
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: a set I ⊆ [k] to glue over, with gluing defined for non-empty I → I : Finset ι together with I.Nonempty; reason: the non-emptiness of I is the domain of the operation in §3.1, not an extra assumption
--   - encoding: H_N(Ψ) for a game with an ordered contradiction of length N → heightParam Ψ N h, with the existence h as an argument; reason: Definition 3.2 defines H_N only for such games
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 3.3, printed p. 11, PDF p. 11

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Definitions.Def_XorParallelRepetition_Exponential_Gluing

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 3.3** (printed/PDF p. 11).  A game with at least one player and an ordered
contradiction of length `N` can be glued over a non-empty set of players so that the glued game
still has an ordered contradiction of length `N` and `H_N` strictly decreases in the
lexicographic order. -/
theorem strict_lex_descent {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) (h : HasOrderedContradiction Ψ N) :
    ∃ I : Finset ι, I.Nonempty ∧ ∃ h' : HasOrderedContradiction (Ψ.glue I) N,
      heightParam (Ψ.glue I) N h' < heightParam Ψ N h := by sorry

end XorParallelRepetition.Exponential
