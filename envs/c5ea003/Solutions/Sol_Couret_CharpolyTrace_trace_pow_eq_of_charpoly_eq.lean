-- Prove2me | solution 1 for Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:20.363815+00:00
-- url     : https://prove2.me/submissions/ef7e14df-708e-48ea-a0a3-69c2d86659f7

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_trace_pow_eq_of_charpoly_eq_of_jacobi
import Theorems.Thm_Matrix_derivative_det_one_sub_X_smul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Abel

/-!
Algebraic bridge from characteristic polynomials to power traces.
This development uses the coefficients of the adjugate of `1 - X A`.
It does not use diagonalizability or an algebraic closure.
-/

noncomputable section

open Polynomial Matrix
open scoped BigOperators

namespace Couret.CharpolyTrace

variable {R : Type*} [CommRing R]
variable {i : Type*} [Fintype i] [DecidableEq i]























/-- Equal characteristic polynomials imply equal traces of every natural
power, over an arbitrary commutative coefficient ring. No diagonalizability
or splitting hypothesis is required. -/
theorem p2m_local_trace_pow_eq_of_charpoly_eq
    (A B : Matrix i i R) (hp : A.charpoly = B.charpoly)
    (k : ℕ) : Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  apply trace_pow_eq_of_charpoly_eq_of_jacobi A B hp
  · simpa only [Matrix.charpolyRev, reverseCharmatrix] using
      Matrix.derivative_det_one_sub_X_smul A
  · simpa only [Matrix.charpolyRev, reverseCharmatrix] using
      Matrix.derivative_det_one_sub_X_smul B

end Couret.CharpolyTrace



universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] {i : Type p2m_u_1} [inst_1 : Fintype.{p2m_u_1} i]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} i] (A B : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R),
  @Eq.{p2m_u_0 + 1}
      (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
      (@Matrix.charpoly.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A)
      (@Matrix.charpoly.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 B) →
    ∀ (k : Nat),
      @Eq.{p2m_u_0 + 1} R
        (@Matrix.trace.{p2m_u_1, p2m_u_0} i R inst_1
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                  (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
          (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
              (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                  (@Matrix.semiring.{p2m_u_0, p2m_u_1} i R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1 inst_2))))
            A k))
        (@Matrix.trace.{p2m_u_1, p2m_u_0} i R inst_1
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                  (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
          (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
              (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                  (@Matrix.semiring.{p2m_u_0, p2m_u_1} i R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1 inst_2))))
            B k)) := @_root_.Couret.CharpolyTrace.p2m_local_trace_pow_eq_of_charpoly_eq

