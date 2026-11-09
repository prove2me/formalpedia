-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_error
-- name    : Couret.STROBO2TORS.recoh_pi_partial_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:53.861199+00:00
-- url     : https://prove2.me/theorems/326c8865-7721-433e-b486-b8277abec289
-- title:
--   Machin sums give a certified rational center for pi
-- statement:
--   For rational x and natural n define A_n(x)=sum_(k<n)(-1)^k x^(2k+1)/(2k+1), E_n(x)=x(x^2)^n/(1-x^2), pi_n=16A_n(1/5)-4A_n(1/239), and e_n=16E_n(1/5)+4E_n(1/239). Rational complex pairs are interpreted by V(a,b)=a+bi. For every natural n, $$|\pi_n-\pi|\le e_n.$$ The same n is used for both arctangent partial sums, including n=0.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalRoots.lean#L63-L89, lines 63–89; source file SHA-256 dc918d91d9f34ce1258fdf43b9d5f7cfbb17e66a2ab684f7e07f0e5f725df81c; theorem Couret.STROBO2TORS.recoh_pi_partial_error

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_arctan_partial_error
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

theorem recoh_pi_partial_error (n : ℕ) :
    |(recohPiPartial n : ℝ) - Real.pi| ≤ (recohPiError n : ℝ) := by sorry
































end Couret.STROBO2TORS
