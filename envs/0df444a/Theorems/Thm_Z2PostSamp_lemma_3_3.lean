-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_3
-- name    : Z2PostSamp.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:47.439503+00:00
-- url     : https://prove2.me/theorems/cc9d92d7-a991-4650-8c58-6bf3cfce2e09
-- title:
--   Lemma 3.3 — unpinned TAP input: the stored centre $v$ estimates $\mathbb E[\theta\theta^\top\mid J]$, overlaps $\to q_0$, local convexity of $\Psi_0$
-- statement:
--   Fix $\lambda>1$. There are an integer $L_{\mathrm{init}}\ge1$ and constants $\gamma_*,c_0,R_0>0$ such that, for any fixed $0<\gamma<\min\{\gamma_*,1\}$, the stored centre $v$ of §2.3 built with $L_{\mathrm{init}}$ spectral AMP steps and step size $\gamma$ satisfies
--
--   $$\frac1n\big\|vv^\top-\mathbb E[\theta\theta^\top\mid J]\big\|_F\xrightarrow{\mathbb P}0,\qquad\frac{\|v\|^2}n\xrightarrow{\mathbb P}q_0,\qquad\frac{|\langle\theta,v\rangle|}n\xrightarrow{\mathbb P}q_0 .$$
--
--   Moreover, with probability tending to one,
--
--   $$\nabla^2\Psi_0(u)\succeq c_0I\quad\text{for every }u\in(-1,1)^n\cap\big(B(v,R_0\sqrt n)\cup B(-v,R_0\sqrt n)\big).$$
--
--   No planted sign is used to compute $v$. Here $\Psi_0$ is the unpinned TAP functional (3.2) and $q_0$ the positive solution of $q=F(\lambda^2q)$. This is the input from Celentano–Fan–Mei that starts the revealing path at a locally convex region.
--
--   **Formalization Note** $\mathbb E[\theta\theta^\top\mid J]=\sum_x\mu_J(x)xx^\top$. Convergence in probability and "with probability tending to one" are written as: the planted probability of a deviation larger than $\varepsilon$, respectively of a failure of the Hessian bound somewhere on the set, tends to $0$. Balls are closed Euclidean balls, and $\nabla^2\Psi_0\succeq c_0I$ is $c_0\|w\|^2\le w^\top\nabla^2\Psi_0(u)w$ with the explicit Hessian form.
--
--   Differences from the source:
--   - encoding: →^P and 'with probability tending to one' → probability of a deviation > ε (resp. of a failure of the Hessian bound on the set) → 0; reason: definitions; the failure-set form does not rely on measurability of the good event
--   - encoding: E[θθᵀ | J] → Σ_x μ_J(x) x xᵀ; reason: the posterior of θ given J is μ_J (Lemma 3.1, Bayes)
--   - encoding: ∇²Ψ₀(u) ⪰ c₀ I → c₀‖w‖² ≤ psi0HessQ (explicit second-derivative form) for every w; reason: the form is the Hessian of (3.2) for symmetric J
--   - reading: the initial center v constructed in Section 2.3 (with the safeguards of App. A) → storedV, the exact-arithmetic vector after L_init AMP steps and n natural-gradient updates, clipped; reason: the lemma refers to the construction of §2.3; its top eigenvector is a fixed choice and every clause is invariant under v ↦ −v
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.3, p.15; (3.2), p.15; §2.3, pp.10–11 (v)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_TAP
import Definitions.Def_Z2PostSamp_Construction

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 3.3 (unpinned TAP input).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.3, p.15: "Fix `λ > 1`. There are an integer `L_init ≥ 1` and constants
`γ_*, c₀, R₀ > 0` such that, for any fixed `0 < γ < min{γ_*, 1}`, the initial center `v` constructed
in Section 2.3 satisfies `(1/n)‖vvᵀ − E[θθᵀ | J]‖_F →^P 0`, `‖v‖²/n →^P q₀`,
`|⟨θ, v⟩|/n →^P q₀`. Moreover, with probability tending to one, `∇²Ψ₀(u) ⪰ c₀ I` for every
`u ∈ (−1,1)ⁿ ∩ (B(v, R₀√n) ∪ B(−v, R₀√n))`. No planted sign is used to compute `v`." `Ψ₀` is (3.2)
and `q₀` the positive solution of (2.9) at `α = 0`.

**Formalization Note.** `v = storedV λ L_init γ J` is the stored vector of §2.3 (spectral AMP for
`L_init` steps, `n` natural-gradient updates with step `γ`, clipped). `E[θθᵀ | J] = Σ_x μ_J(x) x xᵀ`
(the posterior, Lemma 3.1). `→^P` is: for every `ε > 0` the planted probability of a deviation
`> ε` tends to `0`; "with probability tending to one" is: the planted probability that the Hessian
bound fails somewhere on the set tends to `0`. Balls are closed Euclidean balls; `⪰ c₀ I` is
`c₀‖w‖² ≤ wᵀ∇²Ψ₀(u)w` for all `w`. `q₀ = posRoot λ² 0`. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 1 < lam) :
    ∃ Linit : ℕ, 1 ≤ Linit ∧ ∃ γs c₀ R₀ : ℝ, 0 < γs ∧ 0 < c₀ ∧ 0 < R₀ ∧
      ∀ γ : ℝ, 0 < γ → γ < min γs 1 →
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n => plantedLaw n {ω | ε < (1 / (n : ℝ)) *
            Real.sqrt (∑ i, ∑ j, (storedV lam Linit γ (Jof n lam ω) i *
              storedV lam Linit γ (Jof n lam ω) j -
              ∑ x, isingLaw (Jof n lam ω) x * spinValue (x i) * spinValue (x j)) ^ 2)})
          atTop (𝓝 0)) ∧
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n => plantedLaw n {ω | ε <
            |sqNorm (storedV lam Linit γ (Jof n lam ω)) / n - posRoot (lam ^ 2) 0|})
          atTop (𝓝 0)) ∧
        (∀ ε : ℝ, 0 < ε → Tendsto (fun n => plantedLaw n {ω | ε <
            |abs (spinVec ω.1 ⬝ᵥ storedV lam Linit γ (Jof n lam ω)) / n - posRoot (lam ^ 2) 0|})
          atTop (𝓝 0)) ∧
        Tendsto (fun n => plantedLaw n {ω | ¬ ∀ u : Fin n → ℝ, (∀ i, |u i| < 1) →
            (sqNorm (u - storedV lam Linit γ (Jof n lam ω)) ≤ R₀ ^ 2 * n ∨
              sqNorm (u + storedV lam Linit γ (Jof n lam ω)) ≤ R₀ ^ 2 * n) →
            ∀ w : Fin n → ℝ, c₀ * sqNorm w ≤ psi0HessQ lam (Jof n lam ω) u w}) atTop (𝓝 0) := by sorry

end Z2PostSamp
