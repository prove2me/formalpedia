-- Prove2me | Theorems.Thm_EisensteinLogSin_integral_log_one_sub_inv_four_cos_sq_pi_div_six
-- name    : EisensteinLogSin.integral_log_one_sub_inv_four_cos_sq_pi_div_six
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-14T16:22:34.069007+00:00
-- url     : https://prove2.me/theorems/a4546a1f-f173-4ddd-9e16-94ef24a3df62
-- title:
--   $\int_0^{\pi/6} \log\bigl(1 - \tfrac{1}{4\cos^2\theta}\bigr)\,d\theta = -\sqrt3\,L(2,\chi_{-3})/8$
-- statement:
--   A definite integral in Mathlib's terms only:
--
--   $$\int_0^{\pi/6} \log\Bigl(1 - \frac{1}{4\cos^2\theta}\Bigr)\,d\theta = -\frac{\sqrt3}{8}\,L, \qquad L = \sum_{n \ge 0}\Bigl(\frac{1}{(3n+1)^2} - \frac{1}{(3n+2)^2}\Bigr) = L(2, \chi_{-3}).$$
--
--   The identity $\sin 3\theta = \sin\theta\,(4\cos^2\theta - 1)$ writes the integrand as $\log(2\sin 3\theta) - \log(2\sin 2\theta) - \log(2\cos\theta)$, and the integral becomes half of the Clausen value $\int_0^{\pi/3}\log(2\sin u)\,du = -\tfrac{\sqrt3}{4}L$, which is not in Mathlib. That value comes from the Taylor series of $\log(1-z)$ integrated along a circle of radius $r<1$, with $r \to 1$ by Abel's theorem and dominated convergence, and from $\sin(2\pi n/3)$ taking the values $0, \tfrac{\sqrt3}{2}, -\tfrac{\sqrt3}{2}$ on the residue classes modulo $3$. Minus the integral is the volume of the fundamental domain of the Bianchi group $\mathrm{PSL}_2(\mathbb{Z}[\omega])$.
-- source:
--   L. Lewin, Polylogarithms and Associated Functions, North-Holland 1981, Section 4.2 (Clausen function, Cl_2(2π/3) = (√3/2) L(2, χ₋₃)). Formalisation: https://github.com/t4v1/thurston23/blob/main/EisensteinLogSin.lean.

import Mathlib

namespace EisensteinLogSin

theorem integral_log_one_sub_inv_four_cos_sq_pi_div_six :
    ∫ θ in (0:ℝ)..Real.pi / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -(Real.sqrt 3 * (∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) / 8) := by
  sorry

end EisensteinLogSin
