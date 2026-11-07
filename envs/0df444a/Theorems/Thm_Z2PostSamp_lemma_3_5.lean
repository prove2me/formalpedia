-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_5
-- name    : Z2PostSamp.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:36.58694+00:00
-- url     : https://prove2.me/theorems/6a95d029-0234-4430-9bab-261d352b418f
-- title:
--   Lemma 3.5 — positive-side-channel overlap input: $\mathbb E\langle\mathbf 1\{|R_{1\theta}-q|>\varepsilon\}\rangle\le Ce^{-cN}$, uniformly on compact parameter boxes
-- statement:
--   In the Gaussian model of §3.1 let $r\ge0$ and $t>0$, and let $q$ be the positive solution of $q=F(rq+t)$. For every $\varepsilon>0$ there are $C_{r,t,\varepsilon},c_{r,t,\varepsilon}>0$ such that
--
--   $$\mathbb E\big\langle\mathbf 1\{|R_{1\theta}-q|>\varepsilon\}\big\rangle\le C_{r,t,\varepsilon}e^{-c_{r,t,\varepsilon}N},$$
--
--   and the same estimate holds with $R_{1\theta}$ replaced by $R_{12}$. For fixed $r_+<\infty$ and $0<t_-\le t_+<\infty$ the constants can be chosen uniformly over $0\le r\le r_+$ and $t_-\le t\le t_+$.
--
--   The overlap of a posterior sample with the signal, and of two replicas, concentrates exponentially at the replica-symmetric value when the side channel has positive strength. It is the input from El Alaoui–Krzakala–Jordan used at positive revealed fractions.
--
--   **Formalization Note** The uniform statement is formalized (for every box and every $\varepsilon$, constants valid for every $N\ge1$ and every $(r,t)$ in the box); the pointwise statement is the degenerate box. Expectations are lower Lebesgue integrals of posterior averages.
--
--   Differences from the source:
--   - encoding: C_{r,t,ε}, c_{r,t,ε} for each (r, t), and uniform constants on boxes → ∀ box ∀ ε ∃ C c > 0 ∀ N ≥ 1 ∀ (r, t) in the box; reason: the uniform statement contains the pointwise one (degenerate box)
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.5, p.16

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

/-- **Lemma 3.5 (positive-side-channel overlap input), uniform form.**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.5, p.16: "In the Gaussian model above, let `r ≥ 0` and `t > 0`. For every `ε > 0`
there are `C_{r,t,ε}, c_{r,t,ε} > 0` such that `E⟨1{|R_{1θ} − q| > ε}⟩ ≤ C_{r,t,ε} e^{−c_{r,t,ε} N}`. The
same estimate holds with `R_{1θ}` replaced by `R_{12}`. For fixed `r₊ < ∞` and `0 < t₋ ≤ t₊ < ∞`, the
constants can be chosen uniformly over `0 ≤ r ≤ r₊` and `t₋ ≤ t ≤ t₊`."

**Formalization Note.** The uniform statement over the box is stated; the pointwise one is its
special case `r₊ = r`, `t₋ = t₊ = t`. `q = posRoot r t`, `⟨·⟩` is the posterior average (one
replica: `lawMean`; two: `avg2`), `E` the lower Lebesgue integral under the planted law, `N ≥ 1`. -/
theorem lemma_3_5 (rp tm tp : ℝ) (htm : 0 < tm) (htmp : tm ≤ tp) (ε : ℝ) (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ rp → tm ≤ t → t ≤ tp →
      ∫⁻ ω, ENNReal.ofReal (lawMean (gpost r t ω) fun σ =>
          if ε < |overlap σ ω.1 - posRoot r t| then 1 else 0) ∂(gaussLaw N)
        ≤ ENNReal.ofReal (C * Real.exp (-c * N)) ∧
      ∫⁻ ω, ENNReal.ofReal (avg2 (gpost r t ω) fun σ τ =>
          if ε < |overlap σ τ - posRoot r t| then 1 else 0) ∂(gaussLaw N)
        ≤ ENNReal.ofReal (C * Real.exp (-c * N)) := by sorry

end Z2PostSamp
