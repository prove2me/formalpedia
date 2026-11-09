-- Prove2me | solution 1 for Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_via_newton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:33.464315+00:00
-- url     : https://prove2.me/submissions/a1e2a6ab-6da8-4c1e-ae25-f94e3cb0ced4

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
import Theorems.Thm_Couret_CayleyNewton_trace_pow_eq_of_charpoly_eq_of_newton
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — the matrix Newton obligation, discharged from polynomial Jacobi.

The pre-existing `CayleyTwoColourNewton` module proved uniqueness of Newton
recurrences and the conditional spectral classification. This file supplies
its missing single-matrix recurrence, with no new mathematical hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open scoped BigOperators

namespace Couret.CayleyNewton

variable {i : Type*} [Fintype i] [DecidableEq i]





/-- Reuse of the certified recurrence-level bridge, now without any
assumption that the two matrices satisfy Newton's identities. -/
theorem p2m_local_trace_pow_eq_of_charpoly_eq_via_newton
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly) (k : ℕ) :
    Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  exact trace_pow_eq_of_charpoly_eq_of_newton A B hp
    (satisfiesMatrixNewton A) (satisfiesMatrixNewton B) k

end Couret.CayleyNewton


universe p2m_u_0
theorem solution : ∀ {i : Type p2m_u_0} [inst : Fintype.{p2m_u_0} i] [inst_1 : DecidableEq.{p2m_u_0 + 1} i]
  (A B : Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat),
  @Eq.{1} (@Polynomial.{0} Rat (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing i inst_1 inst A)
      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing i inst_1 inst B) →
    ∀ (k : Nat),
      @Eq.{1} Rat
        (@Matrix.trace.{p2m_u_0, 0} i Rat inst Rat.addCommMonoid
          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
            (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
            (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
              (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                  (@Matrix.semiring.{0, p2m_u_0} i Rat Rat.semiring inst inst_1))))
            A k))
        (@Matrix.trace.{p2m_u_0, 0} i Rat inst Rat.addCommMonoid
          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
            (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
            (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
              (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                  (@Matrix.semiring.{0, p2m_u_0} i Rat Rat.semiring inst inst_1))))
            B k)) := @_root_.Couret.CayleyNewton.p2m_local_trace_pow_eq_of_charpoly_eq_via_newton

