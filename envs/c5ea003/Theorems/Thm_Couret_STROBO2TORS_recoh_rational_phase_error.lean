-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rational_phase_error
-- name    : Couret.STROBO2TORS.recoh_rational_phase_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:08.285474+00:00
-- url     : https://prove2.me/theorems/4652c115-dbc3-46f1-a9f4-3d64b47b31f9
-- title:
--   Certified rational centers for unit-interval turns
-- statement:
--   For rational x and natural n define A_n(x)=sum_(k<n)(-1)^k x^(2k+1)/(2k+1), E_n(x)=x(x^2)^n/(1-x^2), pi_n=16A_n(1/5)-4A_n(1/239), and e_n=16E_n(1/5)+4E_n(1/239). Rational complex pairs are interpreted by V(a,b)=a+bi. For rational turn t with |t|≤1, naturals m,n, assume |pi_m|≤4 and n≥15. Set R_(m,n)(t)=T_n(2pi_m t). Then $$|e^{2\pi it}-V(R_{m,n}(t))|\le2e_m+2\,8^n/n!.$$ Negative turns and both endpoints are included; the executable pi-center guard is an explicit hypothesis.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalRoots.lean#L185-L219, lines 185–219; source file SHA-256 dc918d91d9f34ce1258fdf43b9d5f7cfbb17e66a2ab684f7e07f0e5f725df81c; theorem Couret.STROBO2TORS.recoh_rational_phase_error

import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_error
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_exp_taylor_error
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

/-!
Rational centres for complex phases, with explicit analytic error bounds.
The centres use Machin's formula and a finite exponential Taylor polynomial.
All finite arithmetic is rational.  The bounds depend on two natural-number
precision parameters, and therefore can be checked without a real comparison.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

theorem recoh_rational_phase_error (turn : ℚ) (hturn : |turn| ≤ 1)
    (machinTerms taylorTerms : ℕ) (hpi : |recohPiPartial machinTerms| ≤ 4)
    (htaylor : 15 ≤ taylorTerms) :
    ‖Complex.exp (Complex.I * ((2 * Real.pi * (turn : ℝ) : ℝ) : ℂ)) -
      recohRationalComplexValue (recohRationalPhase turn machinTerms taylorTerms)‖ ≤
        (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by sorry


end Couret.STROBO2TORS
