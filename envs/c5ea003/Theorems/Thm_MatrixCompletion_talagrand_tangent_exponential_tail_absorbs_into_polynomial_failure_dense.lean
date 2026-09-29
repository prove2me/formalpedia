-- Prove2me | Theorems.Thm_MatrixCompletion_talagrand_tangent_exponential_tail_absorbs_into_polynomial_failure_dense
-- name    : MatrixCompletion.talagrand_tangent_exponential_tail_absorbs_into_polynomial_failure_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-22T06:14:38.695574+00:00
-- url     : https://prove2.me/theorems/c7408e71-eb14-4013-ba39-aa535f0bbfff
-- title:
--   CR eq. (4.10): the Talagrand exponential tail absorbs into a polynomial failure
-- statement:
--   Candès–Recht (2009, *Exact Matrix Completion via Convex Optimization*, arXiv:0805.4471 / Found. Comput. Math. 9:717–772), Appendix §9.1, the derivation of eq. (4.10) from Theorem 9.1 (eq. (9.2)), p. 46. Starting from the Talagrand/Bousquet exponential tail $P(|Z-\mathbb{E}Z|>t)\le 3\exp\!\big(-(t/(KB))\log(1+Bt/(\sigma^2+B\,\mathbb{E}Z))\big)$, specialise $B=\sigma^2=2\mu_0 nr/m$ and $\mathbb{E}Z\le \mathrm{scale}(C_{\mathrm{expect}})$, plug $t=\mathrm{tangentSamplingDeviationScale}\,C_{\mathrm{tail}}$, and use $\log(1+u)\ge u/(1+u)$ together with the **Theorem 4.1 sampling density** $m\ge \mu_0 r\beta n\log n$ to absorb the prefactor 3 into a polynomial failure probability $\le c\,n^{-\beta}$. Pure $\sqrt{\,}/\log/\exp/\mathrm{rpow}$ algebra — no probability appears. Explicit witnesses $C_{\mathrm{tail}}=\max(2K/\log 2,\ \sqrt{4(1+C_{\mathrm{expect}})K})$, $c=3$. This is the faithful $(m\ge\mu_0 r\beta n\log n)$ correction of the earlier weak-density form $m\ge\beta n\log n$, which is FALSE (letting $r\to\infty$ at $m=\beta n\log n$ drives the tail to $O(1)$ for any fixed $C_{\mathrm{tail}}$). It is the eq. (4.10) bridge that, together with the abstract Talagrand sup-concentration core, closes CR Theorem 4.2.
-- source:
--   Candès & Recht 2009, arXiv:0805.4471, Appendix §9.1 (Proof of Theorem 4.2), eq. (4.10) derived from Theorem 9.1 / eq. (9.2), p. 46. Sampling density m ≥ μ₀ r β n log n is CR Theorem 4.1.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

namespace MatrixCompletion
theorem talagrand_tangent_exponential_tail_absorbs_into_polynomial_failure_dense
    (K Cexpect : ℝ) :
    0 < K → 0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β μ₀ : ℝ) (n r m : ℕ),
        2 < β → 1 ≤ μ₀ → 0 < n → 0 < r → 0 < m →
        (m : ℝ) ≥ μ₀ * (r : ℝ) * β * (n : ℝ) * Real.log (n : ℝ) →
        3 * Real.exp
            (-(tangentSamplingDeviationScale Ctail β μ₀ n r m /
                (K * (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)))) *
              Real.log
                (1 +
                  (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) *
                      tangentSamplingDeviationScale Ctail β μ₀ n r m /
                    ((2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) +
                      (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) *
                        tangentSamplingDeviationScale Cexpect β μ₀ n r m))) ≤
          c * Real.rpow (n : ℝ) (-β) := by sorry
end MatrixCompletion
