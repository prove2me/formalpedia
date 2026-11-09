-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rational_exp_taylor_error
-- name    : Couret.STROBO2TORS.recoh_rational_exp_taylor_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:13.916061+00:00
-- url     : https://prove2.me/theorems/f180d526-e571-4186-b814-6ad68afd373b
-- title:
--   A factorial error bound for phase Taylor sums
-- statement:
--   For rational x and natural n define A_n(x)=sum_(k<n)(-1)^k x^(2k+1)/(2k+1), E_n(x)=x(x^2)^n/(1-x^2), pi_n=16A_n(1/5)-4A_n(1/239), and e_n=16E_n(1/5)+4E_n(1/239). Rational complex pairs are interpreted by V(a,b)=a+bi. For rational t with |t|≤8 and natural n≥15, define T_n(t) as above and b_n=2*8^n/n!. Then $$|e^{it}-V(T_n(t))|\le b_n.$$ Both endpoint values of t are allowed; the threshold n≥15 is explicit.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalRoots.lean#L144-L165, lines 144–165; source file SHA-256 dc918d91d9f34ce1258fdf43b9d5f7cfbb17e66a2ab684f7e07f0e5f725df81c; theorem Couret.STROBO2TORS.recoh_rational_exp_taylor_error

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_exp_taylor_value
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

theorem recoh_rational_exp_taylor_error (t : ℚ) (ht : |t| ≤ 8)
    (n : ℕ) (hn : 15 ≤ n) :
    ‖Complex.exp (Complex.I * (t : ℂ)) -
      recohRationalComplexValue (recohRationalExpTaylor t n)‖ ≤ (recohTaylorError n : ℝ) := by sorry










end Couret.STROBO2TORS
