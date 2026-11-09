-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_no_embedding_iff_ordered_contradiction
-- name    : XorParallelRepetition.Exponential.no_embedding_iff_ordered_contradiction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:16.379342+00:00
-- url     : https://prove2.me/theorems/f4182e0c-bd74-43fe-8209-1e0befd3f209
-- title:
--   Lemma 2.3 — ordered-contradiction equivalence
-- statement:
--   Let $\Psi$ be a generalized XOR game over $\mathbb F_p$, with any number of players, including none. Then
--
--   $$
--   \Psi\ \text{has no commuting embedding}\iff\Psi\ \text{has an ordered contradiction of some length } N.
--   $$
--
--   The equivalence turns an analytic non-existence statement over all Hilbert spaces into a finite combinatorial witness, which the rest of the proof manipulates.
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: a complex Hilbert space, not necessarily finite dimensional → a complete complex inner product space in the universe of the question types, of any dimension; reason: Lean quantifies over types in one universe; nothing is lost, since an embedding in any universe excludes an ordered contradiction (first half of the proof of Lemma 2.3), and without an ordered contradiction that proof builds an embedding on ℓ²(C) in the universe of the question types
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 2.3, printed p. 9, PDF p. 9

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Embedding
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 2.3** (printed/PDF p. 9).  A generalized XOR game has no commuting embeddings if and
only if it has an ordered contradiction. -/
theorem no_embedding_iff_ordered_contradiction {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : GeneralizedXorGame.{u} p ι) :
    ¬ HasCommutingEmbedding Ψ ↔ ∃ N, HasOrderedContradiction Ψ N := by sorry

end XorParallelRepetition.Exponential
