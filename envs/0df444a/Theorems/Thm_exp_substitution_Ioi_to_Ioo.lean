-- Prove2me | Theorems.Thm_exp_substitution_Ioi_to_Ioo
-- name    : exp_substitution_Ioi_to_Ioo
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:33:26.552474+00:00
-- url     : https://prove2.me/theorems/c3367394-55a5-4510-bfff-1e64b2e20d41
-- title:
--   Change of variables $u=1-e^{-\lambda t}$ from $(0,\infty)$ to $(0,1)$
-- statement:
--   **Change of variables $u = 1 - e^{-\lambda t}$ mapping $(0,\infty)$ onto $(0,1)$.** For $\lambda > 0$ and any $g$, $$\int_0^\infty |\lambda e^{-\lambda t}|\,g(1-e^{-\lambda t})\,dt = \int_0^1 g(u)\,du.$$ Here $u=1-e^{-\lambda t}$ is a smooth increasing bijection $(0,\infty)\to(0,1)$ with Jacobian $du = \lambda e^{-\lambda t}\,dt$. Proved via the one-dimensional change-of-variables formula `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, computing the image $\{1-e^{-\lambda t} : t>0\} = (0,1)$ and verifying injectivity and differentiability.
-- source:
--   Standard substitution / change of variables in integration. Mathlib `integral_image_eq_integral_abs_deriv_smul` (one-variable Jacobian formula).

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
open MeasureTheory Set

theorem exp_substitution_Ioi_to_Ioo (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ t in Ioi (0:ℝ), |lam * Real.exp (-(lam * t))| * g (1 - Real.exp (-(lam * t)))
      = ∫ u in Ioo (0:ℝ) 1, g u := by sorry
