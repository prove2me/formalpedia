-- Prove2me | Theorems.Thm_CatalanLogSin_integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three
-- name    : CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:54:30.504003+00:00
-- url     : https://prove2.me/theorems/ac6f8bb0-3278-4abb-a153-92b7293f867f
-- title:
--   $\int_0^{\pi/4} \log\bigl(1 - \tfrac{1}{4\cos^2\theta}\bigr)\,d\theta = -G/3$, $G$ Catalan's constant
-- statement:
--   A definite integral in Mathlib's terms only:
--
--   $$\int_0^{\pi/4} \log\Bigl(1 - \frac{1}{4\cos^2\theta}\Bigr)\,d\theta = -\frac{G}{3}, \qquad G = \sum_{n \ge 0} \frac{(-1)^n}{(2n+1)^2} = 0.9159655\ldots$$
--
--   Catalan's constant appears through the log-sine integral $\int_0^{\pi/4} \log(2\sin\theta)\,d\theta = -G/2$, which Mathlib does not have (it has the value at $\pi/2$). The identity $\sin 3\theta = \sin\theta\,(4\cos^2\theta - 1)$ writes the integrand as $\log(2\sin 3\theta) - \log(2\sin 2\theta) - \log(2\cos\theta)$, whose integrals over $[0, \pi/4]$ are $\tfrac13 \int_0^{3\pi/4}$, $\tfrac12 \int_0^{\pi/2}$ and $\int_{\pi/4}^{\pi/2}$ of $\log(2\sin u)$, worth $G/6$, $0$ and $G/2$. This is the analytic content of Humbert's formula for $\mathbb{Q}(i)$: minus the integral is the volume of the fundamental domain of the Picard group.
-- source:
--   L. Lewin, Polylogarithms and Associated Functions, North-Holland 1981, Section 7.2 (log-sine integrals; Cl_2(π/2) = G). Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/CatalanLogSin.lean#L474-L509.

import Mathlib

namespace CatalanLogSin

theorem integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three :
    ∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -((∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) / 3) := by
  sorry

end CatalanLogSin
