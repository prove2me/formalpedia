-- Prove2me | Theorems.Thm_CatalanLogSin_integral_log_one_sub_inv_four_cos_sq
-- name    : CatalanLogSin.integral_log_one_sub_inv_four_cos_sq
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:27:50.677406+00:00
-- url     : https://prove2.me/theorems/24fbd6fd-caf3-4271-aa22-ec50fbaef3a4
-- title:
--   $\int_0^{\pi/4} \log\bigl(1 - \tfrac{1}{4\cos^2\theta}\bigr)\,d\theta = -G/3$, $G$ Catalan's constant
-- statement:
--   **Superseded.** This statement was published with a dotted declaration name at top level, which the verifier cannot process; the same theorem, in the accepted `namespace` form, is `CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three` (Proved). Please use that one.
--
--   A definite integral in Mathlib's terms only:
--
--   $$\int_0^{\pi/4} \log\Bigl(1 - \frac{1}{4\cos^2\theta}\Bigr)\,d\theta = -\frac{G}{3}, \qquad G = \sum_{n \ge 0} \frac{(-1)^n}{(2n+1)^2}.$$
-- source:
--   L. Lewin, Polylogarithms and Associated Functions, North-Holland 1981, Section 7.2 (log-sine integrals; Cl_2(π/2) = G). Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/CatalanLogSin.lean#L474-L509.

import Mathlib

theorem CatalanLogSin.integral_log_one_sub_inv_four_cos_sq :
    ∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -((∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) / 3) := by
  sorry
