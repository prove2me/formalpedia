-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_eq_4_26_4_27
-- name    : WrightPDIPM.Potential.eq_4_26_4_27
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:14.02611+00:00
-- url     : https://prove2.me/theorems/2e6c2d25-b0a2-4adc-8c88-47c909b318d0
-- title:
--   Eqs. (4.26)–(4.27) — along the PR direction, g₂ ≤ ‖r‖²/((1 − τ)v²_min) and g₁ = −(ρ/(nμ))‖r‖²
-- statement:
--   Let $n \ge 1$, $(x,\lambda,s) \in \mathcal F^\circ$, $\rho > n$, $\tau \in (0,1)$, and let $(\Delta x,\Delta\lambda,\Delta s)$ be the search direction of Algorithm PR: $A\Delta x = 0$, $A^T\Delta\lambda + \Delta s = 0$ (4.12) and $S\Delta x + X\Delta s = -XSe + \frac{n}{\rho}\mu e$ (4.19), where $\mu = x^Ts/n$. With $v_i = (x_is_i)^{1/2}$, $v_{\min} = \min_i v_i$ and $r = -v + \frac n\rho\mu V^{-1}e$ (4.20), the coefficients (4.17) of the quadratic estimate satisfy
--   $$g_2 \le \frac{1}{1-\tau}\frac{\|r\|^2}{v_{\min}^2} \quad (4.26), \qquad g_1 = -\frac{\rho}{n\mu}\|r\|^2 \quad (4.27).$$
--
--   Both coefficients are thereby controlled by the single quantity $\|r\|$, which measures the distance of $(x,s)$ from the target $\frac n\rho\mu$ of the step.
--
--   **Formalization Note** $\rho > n$ is the range of the parameter in (4.2) and Algorithm PR; $n \ge 1$ makes $v_{\min}$ a minimum over a nonempty index set.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 74, Eqs. (4.26) and (4.27)

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Eqs. (4.26) and (4.27)** (Wright, p. 74): the coefficients of the quadratic estimate along
the direction of Algorithm PR. Let `n ≥ 1`, `(x, λ, s) ∈ F°`, `ρ > n`, `τ ∈ (0, 1)`, and let
`(Δx, Δλ, Δs)` solve (4.12) and (4.19). Then
`g₂ ≤ (1/(1 − τ)) ‖r‖²/v_min²` (4.26) and `g₁ = −(ρ/(nμ)) ‖r‖²` (4.27),
with `v_min`, `r` from (4.20). -/
theorem eq_4_26_4_27 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsPRDirection A ρ x s dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    g2 τ x s dx ds ≤ 1 / (1 - τ) * (norm2 (rvec ρ x s) ^ 2 / vmin x s ^ 2) ∧
      g1 ρ x s dx ds = -(ρ / (n * mu x s)) * norm2 (rvec ρ x s) ^ 2 := by sorry

end WrightPDIPM.Potential
