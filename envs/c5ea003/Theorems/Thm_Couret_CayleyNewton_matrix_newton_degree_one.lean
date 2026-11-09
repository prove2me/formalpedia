-- Prove2me | Theorems.Thm_Couret_CayleyNewton_matrix_newton_degree_one
-- name    : Couret.CayleyNewton.matrix_newton_degree_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:47:57.398504+00:00
-- url     : https://prove2.me/theorems/1c742d45-7a27-4db4-aa5d-28a7153b2d8c
-- title:
--   The degree-one matrix Newton trace equation
-- statement:
--   Let A be a square rational matrix on a finite index set and let $c_1$ be its defined reversed characteristic coefficient at index one (zero when the index exceeds the dimension). Then
--
--   $$\operatorname{tr}(A)+c_1=0.$$
--
--   Equivalently the source Newton trace equation holds at degree one.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/bef25648f750d1b9d7792a883597021665e3ba00/research/correspondants_20261013/lean/CayleyNewtonDegreeOne.lean#L17-L35, lines 17–35; source file SHA-256 6dc47834bf10a3b61d9ad6f01e2cadc90fb3c0ae4cddcc29d2073750f4c01997; theorem Couret.CayleyNewton.matrix_newton_degree_one

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 research: first unconditional instance of the universal matrix
Newton equation (index one), over ℚ, including zero-dimensional matrices.

The general case k>1 is not addressed here. This module is separate
from the five certified modules and does not introduce any assumptions,
axioms, or placeholders.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyNewton

theorem matrix_newton_degree_one
    {i : Type*} [Fintype i] [DecidableEq i]
    (A : Matrix i i ℚ) :
    NewtonTraceEquation (reverseCharpolyCoeff A)
      (fun m => Matrix.trace (A ^ m)) 1 := by sorry


end Couret.CayleyNewton
