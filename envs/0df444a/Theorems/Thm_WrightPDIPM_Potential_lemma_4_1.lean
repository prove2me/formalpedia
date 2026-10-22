-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_lemma_4_1
-- name    : WrightPDIPM.Potential.lemma_4_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:02.563543+00:00
-- url     : https://prove2.me/theorems/d73d8e7c-15cd-433a-a751-910704a7f23c
-- title:
--   Lemma 4.1 — log(1 + β) ≤ β, and −Σ log(1 + tᵢ) ≤ −eᵀt + ‖t‖²/(2(1 − τ)) for ‖t‖_∞ ≤ τ < 1
-- statement:
--   Two elementary estimates for the natural logarithm.
--
--   1. For every real $\beta > -1$, $\log(1+\beta) \le \beta$, with equality if and only if $\beta = 0$.
--   2. For every $n$, every $t \in \mathbb R^n$ and every $\tau$ with $\|t\|_\infty \le \tau < 1$,
--   $$-\sum_{i=1}^n \log(1 + t_i) \le -e^Tt + \frac{\|t\|^2}{2(1-\tau)},$$
--   where $e^Tt = \sum_i t_i$ and $\|t\|$ is the Euclidean norm.
--
--   These are the two estimates from which the quadratic upper bound (4.16) on the potential along a search direction is built.
--
--   **Formalization Note** $\|t\|_\infty = \max_i |t_i|$ is `normInf` and $\|t\|$ is `norm2` from the definition file; for $n = 0$ both are $0$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 68, Lemma 4.1 (part (ii) proved in Appendix A, pp. 245–246)

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Lemma 4.1** (Wright, p. 68; part (ii) proved in Appendix A, pp. 245–246).
(i) `log(1 + β) ≤ β` for all `β > −1`, with equality if and only if `β = 0`.
(ii) For any `t ∈ ℝⁿ` with `‖t‖_∞ ≤ τ < 1`,
`−∑ᵢ log(1 + tᵢ) ≤ −eᵀt + ‖t‖²/(2(1 − τ))`, where `‖·‖` is the Euclidean norm. -/
theorem lemma_4_1 :
    (∀ β : ℝ, -1 < β → Real.log (1 + β) ≤ β ∧ (Real.log (1 + β) = β ↔ β = 0)) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (τ : ℝ), normInf t ≤ τ → τ < 1 →
      -∑ i, Real.log (1 + t i) ≤ -∑ i, t i + norm2 t ^ 2 / (2 * (1 - τ))) := by sorry

end WrightPDIPM.Potential
