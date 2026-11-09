-- Prove2me | solution 1 for Couret.CharpolyTrace.trace_mul_adjugateCoeff_eq_of_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:24.127608+00:00
-- url     : https://prove2.me/submissions/6be3a76c-8c9d-4796-a6fe-d7c2d4d41b32

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
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





theorem coeff_trace (M : Matrix i i R[X]) (k : ℕ) :
    (Matrix.trace M).coeff k = Matrix.trace ((matPolyEquiv M).coeff k) := by
  simp [Matrix.trace, Matrix.diag, Polynomial.finset_sum_coeff,
    matPolyEquiv_coeff_apply]













theorem p2m_local_trace_mul_adjugateCoeff_eq_of_jacobi (A : Matrix i i R)
    (hJ : Polynomial.derivative A.charpolyRev =
      -Matrix.trace (A.map C * (reverseCharmatrix A).adjugate)) (k : ℕ) :
    Matrix.trace (A * adjugateCoeff A k) =
      -(A.charpolyRev.coeff (k + 1) * ((k : R) + 1)) := by
  have h := congrArg (fun p : R[X] => p.coeff k) hJ
  dsimp only at h
  rw [Polynomial.coeff_derivative, Polynomial.coeff_neg, coeff_trace,
    map_mul, matPolyEquiv_map_C, Polynomial.coeff_C_mul] at h
  change _ = -Matrix.trace (A * adjugateCoeff A k) at h
  exact neg_eq_iff_eq_neg.mp h.symm





end Couret.CharpolyTrace



universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] {i : Type p2m_u_1} [inst_1 : Fintype.{p2m_u_1} i]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} i] (A : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R),
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
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Semiring.toNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Polynomial.semiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Semiring.toNonAssocSemiring.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Polynomial.semiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
    ∀ (k : Nat),
      @Eq.{p2m_u_0 + 1} R
        (@Matrix.trace.{p2m_u_1, p2m_u_0} i R inst_1
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                  (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
          (@HMul.hMul.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_1} i i i R inst_1
              (@Distrib.toMul.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                      (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst))))))
            A (@Couret.CharpolyTrace.adjugateCoeff.{p2m_u_0, p2m_u_1} R inst i inst_1 inst_2 A k)))
        (@Neg.neg.{p2m_u_0} R
          (@NegZeroClass.toNeg.{p2m_u_0} R
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} R
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} R
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} R
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} R
                    (@Ring.toAddCommGroup.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst)))))))
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            (@Polynomial.coeff.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
              (@Matrix.charpolyRev.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHAdd.{p2m_u_0} R
                (@Distrib.toAdd.{p2m_u_0} R
                  (@instDistribOfSemiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
              (@Nat.cast.{p2m_u_0} R
                (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
                  (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                    (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))
                k)
              (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                (@One.toOfNat1.{p2m_u_0} R
                  (@AddMonoidWithOne.toOne.{p2m_u_0} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                      (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))))) := @_root_.Couret.CharpolyTrace.p2m_local_trace_mul_adjugateCoeff_eq_of_jacobi

