-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_7
-- name    : Z2PostSamp.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:00.270735+00:00
-- url     : https://prove2.me/theorems/8188c620-749d-47eb-91fe-0d9e232b1176
-- title:
--   Lemma 3.7 — uniform overlap after logarithmic pinning: $\mathbb E\langle(R_{12}-q)^2\rangle\le C_\lambda/N$ and (3.15)
-- statement:
--   Fix $\lambda>1$. For $d\in\{0,1\}$ and $k_0\le k<n-d$ set $N=n-k-d$, $r=\lambda^2N/n$ and $t=\lambda^2k/n$. In the Gaussian model of §3.1 let $\sigma^1,\sigma^2$ be independent posterior replicas and $R_{12}=N^{-1}\sum_{i=1}^N\sigma^1_i\sigma^2_i$. Then, uniformly in these choices,
--
--   $$\mathbb E\big\langle(R_{12}-q)^2\big\rangle\le\frac{C_\lambda}N,\qquad q=F(rq+t).\tag{3.14}$$
--
--   If $m=\langle\sigma\rangle$ and $C=\langle(\sigma-m)(\sigma-m)^\top\rangle$ are the posterior mean and covariance, then
--
--   $$\mathbb E\big[\theta^\top C\theta+m^\top Cm+\operatorname{Tr}(C^2)+(\|m\|^2-Nq)^2\big]\le C_\lambda N.\tag{3.15}$$
--
--   Brackets denote posterior averaging, including all replicas displayed inside them. The estimate holds already after logarithmically many revealed coordinates, where the cited signed-overlap estimates degenerate; it is the overlap input of the cavity argument.
--
--   **Formalization Note** One constant serves both bounds and every $n,d,k$. $q$ is the positive root, $m$ the posterior mean and $C$ the published `lawCov`; expectations are lower Lebesgue integrals (the integrand of (3.15) is a sum of nonnegative terms).
--
--   Differences from the source:
--   - encoding: uniformly in these choices → one constant C for all n, d ∈ {0, 1} and k₀ ≤ k < n − d; reason: definition of uniformity
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.7, p.26, (3.14)–(3.15)

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

/-- **Lemma 3.7 (uniform overlap after logarithmic pinning).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.7, p.26: "For `d ∈ {0, 1}` and `k₀ ≤ k < n − d`, set `N = n − k − d`, `r = λ²N/n`, and
`t = λ²k/n`. In the Gaussian model of Section 3.1, let `σ¹, σ²` be independent posterior replicas and
put `R_{12} = N^{−1} Σ_{i=1}^N σ¹_i σ²_i`. Then, uniformly in these choices, `E⟨(R_{12} − q)²⟩ ≤ C_λ/N`,
`q = F(rq + t)` (3.14). If `m = ⟨σ⟩` and `C = ⟨(σ − m)(σ − m)ᵀ⟩` denote the posterior mean and
covariance, then `E[θᵀCθ + mᵀCm + Tr(C²) + (‖m‖² − Nq)²] ≤ C_λ N` (3.15)."

**Formalization Note.** `λ > 1` is fixed (§3); one constant `C_λ` serves both bounds, every `n`, `d`
and `k`. `q = posRoot r t`; `m = postMean`, `C = lawCov` (published) of the posterior; `E` is the
lower Lebesgue integral under the Gaussian model's planted law (the integrand of (3.15) is a sum of
nonnegative terms). -/
theorem lemma_3_7 (lam : ℝ) (hlam : 1 < lam) :
    ∃ C : ℝ, ∀ n d k : ℕ, d ≤ 1 → k0 n lam ≤ k → k < n - d →
      (∫⁻ ω, ENNReal.ofReal (avg2 (gpost (lam ^ 2 * ((n - k - d : ℕ) : ℝ) / n)
            (lam ^ 2 * k / n) ω) fun σ τ =>
          (overlap σ τ - posRoot (lam ^ 2 * ((n - k - d : ℕ) : ℝ) / n) (lam ^ 2 * k / n)) ^ 2)
          ∂(gaussLaw (n - k - d))
        ≤ ENNReal.ofReal (C / ((n - k - d : ℕ) : ℝ))) ∧
      ∫⁻ ω, ENNReal.ofReal
          (let μ := gpost (lam ^ 2 * ((n - k - d : ℕ) : ℝ) / n) (lam ^ 2 * k / n) ω
           let m := postMean μ
           let Cv := lawCov μ
           spinVec ω.1 ⬝ᵥ (Cv *ᵥ spinVec ω.1) + m ⬝ᵥ (Cv *ᵥ m) + (Cv * Cv).trace +
             (sqNorm m - ((n - k - d : ℕ) : ℝ) *
               posRoot (lam ^ 2 * ((n - k - d : ℕ) : ℝ) / n) (lam ^ 2 * k / n)) ^ 2)
          ∂(gaussLaw (n - k - d))
        ≤ ENNReal.ofReal (C * ((n - k - d : ℕ) : ℝ)) := by sorry

end Z2PostSamp
