-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_blr_no_commuting_embedding
-- name    : XorParallelRepetition.Exponential.blr_no_commuting_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:52.422893+00:00
-- url     : https://prove2.me/theorems/b930d717-1a60-45ba-b3c4-e2dcf77c38a4
-- title:
--   Lemma 1.7 — BLR eliminates commuting embeddings
-- statement:
--   Let $\Psi$ be a $k$-XOR game over $\mathbb F_p$ and let $\Psi'$ be its BLR transform. If
--
--   $$
--   \operatorname{val}(\Psi)<1,
--   $$
--
--   then $\Psi'$ has no commuting embedding, on a Hilbert space of any dimension.
--
--   This is the property of the BLR transformation that the proof of the main theorem rests on. It is strictly stronger than the absence of Abelian embeddings (Fact 1.5).
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: val is the maximum acceptance probability → val is the supremum over all deterministic local strategies; reason: it equals the maximum whenever the maximum exists, and no attainment is assumed
--   - generalization: the remark after Theorem 1.3 speaks of k ⩾ 2 → every finite player set, including no player and one player; reason: ι = Fin k with k ⩾ 2 is a special case of the Lean statement
--   - encoding: Ψ′ has the target γ t(x) → Ψ′ is a generalized game whose law samples the target γ t(x) with the questions; reason: the verifier and its acceptance event are unchanged, and the target is not sent to the players
--   - encoding: a complex Hilbert space, not necessarily finite dimensional → a complete complex inner product space in the universe of the question types, of any dimension; reason: Lean quantifies over types in one universe; nothing is lost, since an embedding in any universe excludes an ordered contradiction (first half of the proof of Lemma 2.3), and without an ordered contradiction that proof builds an embedding on ℓ²(C) in the universe of the question types
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 1.7, printed p. 7, PDF p. 7

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR
import Definitions.Def_XorParallelRepetition_Exponential_Embedding

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 1.7** (printed/PDF p. 7).  If `val(Ψ) < 1`, then `Ψ′` has no commuting embedding. -/
theorem blr_no_commuting_embedding {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ¬ HasCommutingEmbedding Ψ.blr := by sorry

end XorParallelRepetition.Exponential
