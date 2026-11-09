-- Prove2me | solution 1 for Couret.CharpolyTrace.trace_pow_eq_of_charpoly_eq_of_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:20:59.601957+00:00
-- url     : https://prove2.me/submissions/f5523ac0-5c3e-4433-8cba-6d0340c2a92a

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_eq_of_jacobi
import Theorems.Thm_Couret_CharpolyTrace_trace_mul_adjugateCoeff_expansion
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





















/-- The exact remaining input of this intermediate lemma is the algebraic
Jacobi formula for the two reverse characteristic matrices. -/
theorem p2m_local_trace_pow_eq_of_charpoly_eq_of_jacobi
    (A B : Matrix i i R) (hp : A.charpoly = B.charpoly)
    (hJA : Polynomial.derivative A.charpolyRev =
      -Matrix.trace (A.map C * (reverseCharmatrix A).adjugate))
    (hJB : Polynomial.derivative B.charpolyRev =
      -Matrix.trace (B.map C * (reverseCharmatrix B).adjugate))
    (k : ℕ) : Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  have hp' : A.charpolyRev = B.charpolyRev := by
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, hp]
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hA := trace_mul_adjugateCoeff_eq_of_jacobi A hJA k
          have hB := trace_mul_adjugateCoeff_eq_of_jacobi B hJB k
          rw [trace_mul_adjugateCoeff_expansion] at hA hB
          have hsum :
              (∑ j ∈ Finset.range k,
                A.charpolyRev.coeff (j + 1) *
                  Matrix.trace (A ^ (k + 1 - (j + 1)))) =
              (∑ j ∈ Finset.range k,
                B.charpolyRev.coeff (j + 1) *
                  Matrix.trace (B ^ (k + 1 - (j + 1)))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hp', ih (k + 1 - (j + 1)) (by omega)]
          rw [hsum, hp'] at hA
          exact add_right_cancel (hA.trans hB.symm)



end Couret.CharpolyTrace



universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] {i : Type p2m_u_1} [inst_1 : Fintype.{p2m_u_1} i]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} i] (A B : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R),
  @Eq.{p2m_u_0 + 1}
      (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
      (@Matrix.charpoly.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A)
      (@Matrix.charpoly.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 B) →
    @Eq.{p2m_u_0 + 1}
        (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
          (@LinearMap.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_0} R R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@RingHom.id.{p2m_u_0} R
              (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Semiring.toNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.semiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Semiring.toNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.semiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
            (@Polynomial.module.{p2m_u_0, p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@Semiring.toModule.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@Polynomial.module.{p2m_u_0, p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@Semiring.toModule.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (fun x =>
            @Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@LinearMap.instFunLike.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_0} R R
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Semiring.toNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.semiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Semiring.toNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.semiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
            (@Polynomial.module.{p2m_u_0, p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@Semiring.toModule.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@Polynomial.module.{p2m_u_0, p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@Semiring.toModule.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@RingHom.id.{p2m_u_0} R
              (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@Polynomial.derivative.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@Matrix.charpolyRev.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A))
        (@Neg.neg.{p2m_u_0}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@Polynomial.instNeg.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))
          (@Matrix.trace.{p2m_u_1, p2m_u_0} i
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            inst_1
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@CommRing.toNonUnitalCommRing.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Polynomial.commRing.{p2m_u_0} R inst))))))
            (@HMul.hMul.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_1} i i i
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                inst_1
                (@Polynomial.instMul.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0}
                        (@Polynomial.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                        (@CommRing.toNonUnitalCommRing.{p2m_u_0}
                          (@Polynomial.{p2m_u_0} R
                            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                          (@Polynomial.commRing.{p2m_u_0} R inst)))))))
              (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} i i R
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                A
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                  (@RingHom.{p2m_u_0, p2m_u_0} R
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Semiring.toNonAssocSemiring.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Polynomial.semiring.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                  R
                  (fun x =>
                    @Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@RingHom.instFunLike.{p2m_u_0, p2m_u_0} R
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Semiring.toNonAssocSemiring.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Polynomial.semiring.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                  (@Polynomial.C.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
              (@Matrix.adjugate.{p2m_u_1, p2m_u_0} i
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                inst_2 inst_1 (@Polynomial.commRing.{p2m_u_0} R inst)
                (@Couret.CharpolyTrace.reverseCharmatrix.{p2m_u_0, p2m_u_1} R inst i inst_2 A))))) →
      @Eq.{p2m_u_0 + 1}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
            (@LinearMap.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_0} R R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@RingHom.id.{p2m_u_0} R
                (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Semiring.toNonAssocSemiring.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.semiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Semiring.toNonAssocSemiring.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.semiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
              (@Polynomial.module.{p2m_u_0, p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
                (@Semiring.toModule.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Polynomial.module.{p2m_u_0, p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
                (@Semiring.toModule.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (fun x =>
              @Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@LinearMap.instFunLike.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_0} R R
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Semiring.toNonAssocSemiring.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.semiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Semiring.toNonAssocSemiring.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.semiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
              (@Polynomial.module.{p2m_u_0, p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
                (@Semiring.toModule.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Polynomial.module.{p2m_u_0, p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
                (@Semiring.toModule.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@RingHom.id.{p2m_u_0} R
                (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            (@Polynomial.derivative.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Matrix.charpolyRev.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 B))
          (@Neg.neg.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Polynomial.instNeg.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))
            (@Matrix.trace.{p2m_u_1, p2m_u_0} i
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              inst_1
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@CommRing.toNonUnitalCommRing.{p2m_u_0}
                        (@Polynomial.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                        (@Polynomial.commRing.{p2m_u_0} R inst))))))
              (@HMul.hMul.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_1} i i i
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  inst_1
                  (@Polynomial.instMul.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0}
                        (@Polynomial.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0}
                          (@Polynomial.{p2m_u_0} R
                            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                          (@CommRing.toNonUnitalCommRing.{p2m_u_0}
                            (@Polynomial.{p2m_u_0} R
                              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                            (@Polynomial.commRing.{p2m_u_0} R inst)))))))
                (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} i i R
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  B
                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                    (@RingHom.{p2m_u_0, p2m_u_0} R
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Semiring.toNonAssocSemiring.{p2m_u_0}
                        (@Polynomial.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                        (@Polynomial.semiring.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                    R
                    (fun x =>
                      @Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@RingHom.instFunLike.{p2m_u_0, p2m_u_0} R
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Semiring.toNonAssocSemiring.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Semiring.toNonAssocSemiring.{p2m_u_0}
                        (@Polynomial.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                        (@Polynomial.semiring.{p2m_u_0} R
                          (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                    (@Polynomial.C.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                (@Matrix.adjugate.{p2m_u_1, p2m_u_0} i
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  inst_2 inst_1 (@Polynomial.commRing.{p2m_u_0} R inst)
                  (@Couret.CharpolyTrace.reverseCharmatrix.{p2m_u_0, p2m_u_1} R inst i inst_2 B))))) →
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
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1
                        inst_2))))
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
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1
                        inst_2))))
                B k)) := @_root_.Couret.CharpolyTrace.p2m_local_trace_pow_eq_of_charpoly_eq_of_jacobi

