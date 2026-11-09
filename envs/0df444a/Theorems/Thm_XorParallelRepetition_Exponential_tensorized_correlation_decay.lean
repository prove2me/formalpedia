-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_tensorized_correlation_decay
-- name    : XorParallelRepetition.Exponential.tensorized_correlation_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:12.610342+00:00
-- url     : https://prove2.me/theorems/3a0a1a08-ba8a-4268-af37-3ed1f0fa4287
-- title:
--   Lemma 3.5 — tensorized correlation decay (corrected: zero-player constant-target obstruction excluded)
-- statement:
--   Let $\Psi$ be a generalized XOR game that has an ordered contradiction of length $N$, and suppose that $\Psi$ has at least one player, or that two supported challenges of $\Psi$ have different right hand sides. Then there is $\varepsilon=\varepsilon(N,\Psi)>0$ such that for all $n,d\in\mathbb N$, all $a_1,\dots,a_n\in\mathbb F_p$ with $a_j\ne0$ for at least $d$ of the coordinates, and all functions $f_i:\Sigma_i^n\to\mathbb C$ with $|f_i|\le1$ pointwise,
--
--   $$
--   \left|\mathbb E_{(x_1,\dots,x_k,t)\sim\mu_\Psi^{\otimes n}}\left[\prod_{i}f_i(x_i)\ \prod_{j=1}^{n}\omega_p^{a_jt_j}\right]\right|\le(1-\varepsilon)^d.
--   $$
--
--   Here $x_i\in\Sigma_i^n$ is the block of player $i$ and $t\in\mathbb F_p^n$ is the vector of right hand sides. The constant is fixed before $n$, $d$, the coefficients and the functions.
--
--   The bound is the direct-sum estimate that Claim 4.1 sums over all characters.
--
--   Differences from the source:
--   - correction: every generalized game with an ordered contradiction of length N → the added hypothesis: at least one player, or two supported challenges with different right hand sides; reason: Definition 2.1 allows k = 0, and for p = 2 the point mass on t = 1 has the ordered contradiction of length 1 consisting of that challenge with sign +1; with n = d = 1 and a₁ = 1 the left side is |E ω₂^t| = 1, which is not at most 1 - ε for any ε > 0; the hypothesis excludes exactly the zero-player constant-target games
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: expectation E under a discrete distribution → the absolutely convergent series expect, weighting each outcome by its mass; reason: every integrand here is bounded by 1, so the series is the expectation
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 3.5, printed p. 13, PDF p. 13

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_Games
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 3.5** (printed/PDF p. 13), corrected for the zero-player constant-target obstruction.
The constant `ε` is chosen after the game and `N`, and before `n`, `d`, the coefficients and the
block functions. -/
theorem tensorized_correlation_decay {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) (h : HasOrderedContradiction Ψ N)
    (hnd : Nonempty ι ∨ Ψ.HasTwoTargets) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n d : ℕ) (a : Fin n → ZMod p),
      d ≤ (Finset.univ.filter fun j => a j ≠ 0).card →
      ∀ f : ∀ i, (Fin n → Ψ.Q i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
        ‖expect (iidPMF Ψ.μ n) fun s =>
          (∏ i, f i fun j => (s j).1 i) * ∏ j, phase p (a j * (s j).2)‖ ≤ (1 - ε) ^ d := by sorry

end XorParallelRepetition.Exponential
