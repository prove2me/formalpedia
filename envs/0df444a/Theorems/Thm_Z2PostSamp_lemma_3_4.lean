-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_4
-- name    : Z2PostSamp.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:56.205531+00:00
-- url     : https://prove2.me/theorems/6ae307f2-27cb-409a-a927-0b2e432c33cf
-- title:
--   Lemma 3.4 — positive-side-channel TAP input: AMP state evolution and local convexity of $\Phi$ near $u^L$
-- statement:
--   Fix $r,t>0$ and consider the Gaussian model of §3.1 with $q=F(rq+t)$ and
--
--   $$\Phi(u)=\sum_{i=1}^N\phi(u_i)-\tfrac12u^\top Au-h^\top u+\frac{r(1-q)}2\|u\|^2,\qquad u\in(-1,1)^N .$$
--
--   Initialize $z^0=h$, $u^{-1}=0$ and use $u^\ell=\tanh z^\ell$, $z^{\ell+1}=Au^\ell+h-r\big(1-\frac{\|u^\ell\|^2}N\big)u^{\ell-1}$. If $s_0=t$ and $s_{\ell+1}=rF(s_\ell)+t$, then:
--
--   1. for every fixed $L\ge0$, $\ \|u^L\|^2/N\xrightarrow{\mathbb P}F(s_L)$ and $\langle\theta,u^L\rangle/N\xrightarrow{\mathbb P}F(s_L)$ as $N\to\infty$;
--   2. $F(s_L)\uparrow q$ as $L\to\infty$;
--   3. there are $c,R>0$, depending only on $r,t$, such that for each fixed $0<\varepsilon<R$ and every sufficiently large fixed $L$,
--   $$\mathbb P\Big(\nabla^2\Phi(u)\succeq cI_N\text{ for every }u\in(-1,1)^N\cap B(u^L,\varepsilon\sqrt N)\Big)\to1 .$$
--
--   The order of quantifiers is that $\varepsilon$ and then $L$ are fixed before $N\to\infty$. This is the input from Celentano used to build the checkpoint centres.
--
--   **Formalization Note** $q$ is the positive root. Convergence in probability and "→ 1" are written as vanishing probabilities of deviation, respectively of failure of the Hessian bound somewhere on the set. $F(s_L)\uparrow q$ is monotonicity in $L$ together with convergence to $q$. The Hessian is the explicit form.
--
--   Differences from the source:
--   - encoding: →^P and P(… for every u …) → 1 → probability of a deviation > ε (resp. of a failure of the Hessian bound on the set) → 0; reason: definitions
--   - encoding: F(s_L) ↑ q as L → ∞ → Monotone (L ↦ F(s_L)) and F(s_L) → posRoot r t; reason: definition of ↑
--   - encoding: ∇²Φ(u) ⪰ c I_N → c‖v‖² ≤ gaussHessQ (explicit second-derivative form) for every v; reason: the form is the Hessian of Φ (A symmetric)
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.4, pp.15–16

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_Construction
import Definitions.Def_Z2PostSamp_GaussModel

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 3.4 (positive-side-channel TAP input).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.4, pp.15–16: "Fix `r, t > 0` and consider the Gaussian model defined above, with
`q = F(rq + t)`. Define `Φ(u) = Σ_{i=1}^N φ(u_i) − ½ uᵀAu − hᵀu + (r(1 − q)/2)‖u‖²`,
`u ∈ (−1,1)^N`. Initialize `z⁰ = h`, `u^{−1} = 0`, and use `u^ℓ = tanh z^ℓ`,
`z^{ℓ+1} = Au^ℓ + h − r(1 − ‖u^ℓ‖²/N) u^{ℓ−1}`. If `s₀ = t` and `s_{ℓ+1} = rF(s_ℓ) + t`, then, for every
fixed `L ≥ 0`, `‖u^L‖²/N →^P F(s_L)`, `⟨θ, u^L⟩/N →^P F(s_L)`, `F(s_L) ↑ q` as `L → ∞`. There are
`c, R > 0`, depending only on `r, t`, such that, for each fixed `0 < ε < R` and every sufficiently
large fixed `L`, `P(∇²Φ(u) ⪰ cI_N for every u ∈ (−1,1)^N ∩ B(u^L, ε√N)) → 1`. The order of
quantifiers is that `ε` and then `L` are fixed before `N → ∞`."

**Formalization Note.** `q = posRoot r t`. `→^P` and "→ 1" are written as: the probability of a
deviation `> ε` (resp. of the failure of the Hessian bound somewhere on the set) tends to `0` as
`N → ∞`. `F(s_L) ↑ q` is monotonicity in `L` together with convergence to `q`. The Hessian of `Φ` is
the explicit form `gaussHessQ`; the ball is the closed Euclidean ball. The quantifier order is the
printed one: `c, R`, then `ε`, then `L₀`, then `L ≥ L₀`, then `N → ∞`. -/
theorem lemma_3_4 (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    (∀ L : ℕ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ => gaussLaw N {ω | ε <
        |sqNorm (gaussAmpU r t ω L) / N - Fch (seIter r t L)|}) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => gaussLaw N {ω | ε <
        |(spinVec ω.1 ⬝ᵥ gaussAmpU r t ω L) / N - Fch (seIter r t L)|}) atTop (𝓝 0)) ∧
    Monotone (fun L => Fch (seIter r t L)) ∧
    Tendsto (fun L => Fch (seIter r t L)) atTop (𝓝 (posRoot r t)) ∧
    ∃ c R : ℝ, 0 < c ∧ 0 < R ∧ ∀ ε : ℝ, 0 < ε → ε < R → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      Tendsto (fun N : ℕ => gaussLaw N {ω | ¬ ∀ u : Fin N → ℝ, (∀ i, |u i| < 1) →
          sqNorm (u - gaussAmpU r t ω L) ≤ ε ^ 2 * N →
          ∀ v : Fin N → ℝ, c * sqNorm v ≤ gaussHessQ r t (Amat r ω) u v}) atTop (𝓝 0) := by sorry

end Z2PostSamp
