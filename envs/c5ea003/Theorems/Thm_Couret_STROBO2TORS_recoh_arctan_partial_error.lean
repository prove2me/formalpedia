-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_arctan_partial_error
-- name    : Couret.STROBO2TORS.recoh_arctan_partial_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:52.376213+00:00
-- url     : https://prove2.me/theorems/3bbcc203-1186-4c84-b349-681417730aa7
-- title:
--   Geometric error bound for rational arctangent sums
-- statement:
--   For rational x and natural n define A_n(x)=sum_(k<n)(-1)^k x^(2k+1)/(2k+1), E_n(x)=x(x^2)^n/(1-x^2), pi_n=16A_n(1/5)-4A_n(1/239), and e_n=16E_n(1/5)+4E_n(1/239). Rational complex pairs are interpreted by V(a,b)=a+bi. For rational x with 0≤x<1 and natural n, $$|A_n(x)-\arctan x|\le E_n(x).$$ The bound includes x=0 and n=0.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalRoots.lean#L27-L55, lines 27–55; source file SHA-256 dc918d91d9f34ce1258fdf43b9d5f7cfbb17e66a2ab684f7e07f0e5f725df81c; theorem Couret.STROBO2TORS.recoh_arctan_partial_error

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

theorem recoh_arctan_partial_error (x : ℚ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    |(recohArctanPartial x n : ℝ) - Real.arctan (x : ℝ)| ≤
      (recohArctanError x n : ℝ) := by sorry






































end Couret.STROBO2TORS
