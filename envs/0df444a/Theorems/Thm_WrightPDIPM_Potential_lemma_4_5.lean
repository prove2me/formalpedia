-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_lemma_4_5
-- name    : WrightPDIPM.Potential.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:11.790878+00:00
-- url     : https://prove2.me/theorems/226c3907-3f58-4dab-8ad8-e716e3129122
-- title:
--   Lemma 4.5 — ‖r‖ ≥ (√3/(2v_min))(nμ/ρ) for ρ > n + √n
-- statement:
--   Let $n \ge 1$, $(x,\lambda,s) \in \mathcal F^\circ$, $\mu = x^Ts/n$, $v_i = (x_is_i)^{1/2}$, $v_{\min} = \min_i v_i$ and $r = -v + \frac n\rho\mu V^{-1}e$ (4.20). For every $\rho > n + \sqrt n$,
--   $$\|r\| \ge \frac{\sqrt3}{2v_{\min}}\cdot\frac{n\mu}{\rho}. \qquad (4.28)$$
--
--   This lower bound on $\|r\|$ is what makes the linear coefficient $g_1 = -\frac{\rho}{n\mu}\|r\|^2$ of the quadratic estimate negative enough for a fixed decrease of the potential.
--
--   **Formalization Note** The hypothesis is the book's strict $\rho > n + \sqrt n$, as printed. A companion item (`lemma_4_5_strong`) poses the same bound for $\rho \ge n + \sqrt n$, which the book uses in Theorem 4.6 and Corollary 4.7. $n \ge 1$ is implicit in the book ($v_{\min}$ is a minimum over the indices).
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 75, Lemma 4.5

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Lemma 4.5** (Wright, p. 75). For any `(x, λ, s) ∈ F°` and for `ρ > n + √n`,
`‖r‖ ≥ (√3/(2v_min)) · (nμ/ρ)` (4.28), with `v_min`, `r` from (4.20) and `μ = xᵀs/n`
(`n ≥ 1`). -/
theorem lemma_4_5 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n < ρ) :
    Real.sqrt 3 / (2 * vmin x s) * (n * mu x s / ρ) ≤ norm2 (rvec ρ x s) := by sorry

end WrightPDIPM.Potential
