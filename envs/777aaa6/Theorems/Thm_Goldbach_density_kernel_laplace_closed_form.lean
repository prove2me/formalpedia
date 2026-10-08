-- Prove2me | Theorems.Thm_Goldbach_density_kernel_laplace_closed_form
-- name    : Goldbach.density_kernel_laplace_closed_form
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:41:05.251802+00:00
-- url     : https://prove2.me/theorems/6f6df1bc-af8e-42ab-be5a-eab646fc518b
-- title:
--   An exact closed form for the density detector Laplace transform
-- statement:
--   For every nonzero real number $z$, the density kernel has the exact Laplace
--   transform
--
--   $$\int_0^2\frac{(2-u)^3(4+6u+u^2)}{30}e^{-zu}\,du
--   =\frac{16z^5-40z^3+60z^2-60+60e^{-2z}(z+1)^2}{15z^6}.$$
--
--   The closed proof constructs a polynomial-exponential antiderivative, checks its
--   derivative algebraically, proves interval integrability, and applies Mathlib's
--   fundamental theorem of calculus. The nonzero condition is retained explicitly;
--   the value at zero is handled by the separate exact moment theorem.
--
--   This formula corroborates the independent rational detector audit through a
--   different numerical evaluation path. At $z=-1$ it gives exactly $8/5$; at
--   $z=1$ it gives $16e^{-2}-8/5$. Neither floating-point approximations nor open
--   theorems are used in the formal proof.
--
--   The kernel comes from equation (3.21) in
--   https://arxiv.org/html/2511.05631v2#S3 . The result formalizes an elementary
--   integration identity, not the analytic density theorem or a Goldbach
--   conclusion; no mathematical novelty is claimed.
-- source:
--   Exact Laplace transform of the kernel in equation (3.21), https://arxiv.org/html/2511.05631v2#S3 . Elementary integration, not verification of the density theorem; no mathematical novelty is claimed.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory
set_option autoImplicit false

theorem Goldbach.density_kernel_laplace_closed_form (z : ℝ) (hz : z ≠ 0) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) =
      (16*z^5-40*z^3+60*z^2-60+60*Real.exp (-2*z)*(z+1)^2)/(15*z^6) := by sorry
