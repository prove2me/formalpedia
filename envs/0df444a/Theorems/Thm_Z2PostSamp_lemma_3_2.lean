-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_2
-- name    : Z2PostSamp.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:55.123747+00:00
-- url     : https://prove2.me/theorems/2186737e-a3c6-46a8-80bc-1a5c2b7d0a0c
-- title:
--   Lemma 3.2 — unpinned absolute-overlap input: $\mathbb E\langle\mathbf 1\{||R_{1\theta}|-q|>\varepsilon\}\rangle\le Ce^{-cN}$ at $t=0$, $r>1$
-- statement:
--   In the Gaussian model of §3.1 let $t=0$ and $r>1$, and let $q$ be the positive solution of $q=F(rq)$. For every $\varepsilon>0$ there are $C_{r,\varepsilon},c_{r,\varepsilon}>0$ such that
--
--   $$\mathbb E\Big\langle\mathbf 1\big\{\big||R_{1\theta}|-q\big|>\varepsilon\big\}\Big\rangle\le C_{r,\varepsilon}e^{-c_{r,\varepsilon}N},$$
--
--   and the same estimate holds with $R_{1\theta}$ replaced by $R_{12}$. The constants can be chosen uniformly for $r$ in any fixed compact subinterval of $(1,\infty)$.
--
--   Without side information only the magnitude of the overlap concentrates (the posterior keeps the global sign symmetry). This is the El Alaoui–Krzakala–Jordan input that controls the start of the revealing path.
--
--   **Formalization Note** The uniform statement over $[r_1,r_2]\subset(1,\infty)$ is formalized; a fixed $r$ is the case $r_1=r_2=r$. Expectations are lower Lebesgue integrals of posterior averages, $N\ge1$.
--
--   Differences from the source:
--   - encoding: constants for each r > 1, uniform on compact subintervals of (1, ∞) → ∀ [r₁, r₂] ⊂ (1, ∞) ∀ ε ∃ C c > 0 ∀ N ≥ 1 ∀ r ∈ [r₁, r₂]; reason: the uniform statement contains the pointwise one
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.2, p.15

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

/-- **Lemma 3.2 (unpinned absolute-overlap input), uniform form.**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.2, p.15: "In the Gaussian model above, let `t = 0` and `r > 1`. For every `ε > 0`
there are `C_{r,ε}, c_{r,ε} > 0` such that `E⟨1{||R_{1θ}| − q| > ε}⟩ ≤ C_{r,ε} e^{−c_{r,ε} N}`. The same
estimate holds with `R_{1θ}` replaced by `R_{12}`. The constants can be chosen uniformly for `r` in
any fixed compact subinterval of `(1, ∞)`."

**Formalization Note.** The uniform statement over `[r₁, r₂] ⊂ (1, ∞)` is stated; the fixed-`r`
statement is the case `r₁ = r₂ = r`. `q = posRoot r 0`, the unique positive solution of
`q = F(rq)` (§3.1). `⟨·⟩` is the posterior average, `E` the lower Lebesgue integral, `N ≥ 1`. -/
theorem lemma_3_2 (r₁ r₂ : ℝ) (h1 : 1 < r₁) (h12 : r₁ ≤ r₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ r : ℝ, r₁ ≤ r → r ≤ r₂ →
      ∫⁻ ω, ENNReal.ofReal (lawMean (gpost r 0 ω) fun σ =>
          if ε < |abs (overlap σ ω.1) - posRoot r 0| then 1 else 0) ∂(gaussLaw N)
        ≤ ENNReal.ofReal (C * Real.exp (-c * N)) ∧
      ∫⁻ ω, ENNReal.ofReal (avg2 (gpost r 0 ω) fun σ τ =>
          if ε < |abs (overlap σ τ) - posRoot r 0| then 1 else 0) ∂(gaussLaw N)
        ≤ ENNReal.ofReal (C * Real.exp (-c * N)) := by sorry

end Z2PostSamp
