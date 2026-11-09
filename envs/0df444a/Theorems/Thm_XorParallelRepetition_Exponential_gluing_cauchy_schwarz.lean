-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_gluing_cauchy_schwarz
-- name    : XorParallelRepetition.Exponential.gluing_cauchy_schwarz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:06:10.503907+00:00
-- url     : https://prove2.me/theorems/0b56e2f4-0b68-4d7c-9044-b219eef19103
-- title:
--   Lemma 3.1 — one gluing Cauchy–Schwarz inequality
-- statement:
--   Let $\Psi$ be a generalized XOR game with law $\mu_\Psi$, and let $I$ be a non-empty set of players, with $\mu_{\Psi_{\mathrm{glue}(I)}}$ the law of the glued game. For every $a\in\mathbb F_p$ and all functions $f_i:\Sigma_i\to\mathbb C$ with $|f_i|\le1$ pointwise,
--
--   $$
--   \left|\mathbb E_{(x,t)\sim\mu_\Psi}\left[\prod_{i}f_i(x_i)\,\omega_p^{-at}\right]\right|^2
--   \le
--   \left|\mathbb E_{(y,u)\sim\mu_{\Psi_{\mathrm{glue}(I)}}}\left[\prod_{i\notin I}f_i(y_i)\overline{f_i(y_{i'})}\,\omega_p^{-au}\right]\right|.
--   $$
--
--   The conjugation is on the second factor of each pair only, and $a=0$ is allowed. This is the single analytic step of the proof: each gluing costs one squaring of the correlation.
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: a set I ⊆ [k] to glue over, with gluing defined for non-empty I → I : Finset ι together with I.Nonempty; reason: the non-emptiness of I is the domain of the operation in §3.1, not an extra assumption
--   - encoding: expectation E under a discrete distribution → the absolutely convergent series expect, weighting each outcome by its mass; reason: every integrand here is bounded by 1, so the series is the expectation
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 3.1, printed p. 11, PDF p. 11

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Gluing

open scoped ComplexConjugate

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 3.1** (printed/PDF p. 11).  One application of gluing costs one Cauchy–Schwarz
inequality.  The second factor of each pair carries the complex conjugate. -/
theorem gluing_cauchy_schwarz {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι) (hI : I.Nonempty) (a : ZMod p)
    (f : ∀ i, Ψ.Q i → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖expect Ψ.μ fun ω => (∏ i, f i (ω.1 i)) * phase p (-(a * ω.2))‖ ^ 2 ≤
      ‖expect (Ψ.glue I).μ fun ω =>
        (∏ i : {i // i ∉ I}, f i.1 (ω.1 (i, false)) * conj (f i.1 (ω.1 (i, true)))) *
          phase p (-(a * ω.2))‖ := by sorry

end XorParallelRepetition.Exponential
