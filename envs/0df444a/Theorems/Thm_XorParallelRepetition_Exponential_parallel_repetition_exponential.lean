-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_parallel_repetition_exponential
-- name    : XorParallelRepetition.Exponential.parallel_repetition_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:42.605694+00:00
-- url     : https://prove2.me/theorems/710deaa8-bf82-49cc-8eea-2a9d0faf4c93
-- title:
--   Theorem 1.3 — exponential decay of repeated XOR games
-- statement:
--   Let $p$ be a prime and let $\Psi$ be a $k$-XOR game over $\mathbb F_p$: a verifier samples $x\sim\mu$ from a joint law on $\Sigma_1\times\dots\times\Sigma_k$, sends $x_i$ to player $i$, receives $a_i\in\mathbb F_p$ and accepts exactly when $a_1+\dots+a_k=t(x)$. If $\operatorname{val}(\Psi)<1$, then there is $\varepsilon=\varepsilon(\Psi)>0$ such that
--
--   $$
--   \operatorname{val}(\Psi^{\otimes n})\le(1-\varepsilon)^n\qquad\text{for all }n\in\mathbb N.
--   $$
--
--   The constant is chosen once for the game, before $n$. In $\Psi^{\otimes n}$ the $n$ samples are independent, the correlations of $\mu$ between players are kept inside each sample, every player may answer as an arbitrary function of its whole block, and the verifier requires the equation in every coordinate. No assumption on $\mu$ is made.
--
--   This is the main result of the paper, and it extends exponential decay from some 3-XOR games to all XOR games over prime fields.
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: val is the maximum acceptance probability → val is the supremum over all deterministic local strategies; reason: it equals the maximum whenever the maximum exists, and no attainment is assumed
--   - generalization: the remark after Theorem 1.3 speaks of k ⩾ 2 → every finite player set, including no player and one player; reason: ι = Fin k with k ⩾ 2 is a special case of the Lean statement
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Theorem 1.3, printed p. 4, PDF p. 4

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames

namespace XorParallelRepetition.Exponential

universe u

/-- **Theorem 1.3** (printed/PDF p. 4).  If `Ψ` is a `k`-XOR game with `val(Ψ) < 1`, then there is
`ε = ε(Ψ) > 0` such that `val(Ψ^{⊗n}) ≤ (1 - ε)^n` for all `n ∈ ℕ`. -/
theorem parallel_repetition_exponential {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, Ψ.repVal n ≤ (1 - ε) ^ n := by sorry

end XorParallelRepetition.Exponential
