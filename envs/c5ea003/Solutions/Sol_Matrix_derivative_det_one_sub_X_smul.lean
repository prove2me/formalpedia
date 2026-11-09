-- Prove2me | solution 1 for Matrix.derivative_det_one_sub_X_smul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:21.373837+00:00
-- url     : https://prove2.me/submissions/8d1a0c24-6102-4e05-b0fb-b80ba1f5aecc

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorems.Thm_Matrix_derivative_det_polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset Polynomial Matrix

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]







theorem p2m_local_derivative_det_one_sub_X_smul (M : Matrix n n R) :
    derivative (det (1 - (X : R[X]) • M.map C)) =
      - trace (M.map C * adjugate (1 - (X : R[X]) • M.map C)) := by
  rw [derivative_det_polynomial]
  have hd : (1 - (X : R[X]) • M.map C).map derivative = -(M.map C) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [hd, neg_mul, trace_neg]


end Matrix

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} {n : Type p2m_u_1} [inst : CommRing.{p2m_u_0} R] [inst_1 : Fintype.{p2m_u_1} n]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} n] (M : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n R),
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
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Semiring.toNonAssocSemiring.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Polynomial.semiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Semiring.toNonAssocSemiring.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Polynomial.semiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
      (@Matrix.det.{p2m_u_0, p2m_u_1} n inst_2 inst_1
        (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
        (@Polynomial.commRing.{p2m_u_0} R inst)
        (@HSub.hSub.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (@instHSub.{max p2m_u_0 p2m_u_1}
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@Matrix.sub.{p2m_u_0, p2m_u_1, p2m_u_1} n n
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@Polynomial.instSub.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))
          (@OfNat.ofNat.{max p2m_u_0 p2m_u_1}
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (nat_lit 1)
            (@One.toOfNat1.{max p2m_u_0 p2m_u_1}
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Matrix.one.{p2m_u_0, p2m_u_1} n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                inst_2
                (@Polynomial.instZero.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Polynomial.instOne.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
          (@HSMul.hSMul.{p2m_u_0, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
            (@instHSMul.{p2m_u_0, max p2m_u_0 p2m_u_1}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@Matrix.smul.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@instSMulOfMul.{p2m_u_0}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.instMul.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
            (@Polynomial.X.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} n n R
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              M
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
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))))))
    (@Neg.neg.{p2m_u_0}
      (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
      (@Polynomial.instNeg.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))
      (@Matrix.trace.{p2m_u_1, p2m_u_0} n
        (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
        inst_1
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
            (@Polynomial.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_1} n n n
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
          (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} n n R
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            M
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
          (@Matrix.adjugate.{p2m_u_1, p2m_u_0} n
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            inst_2 inst_1 (@Polynomial.commRing.{p2m_u_0} R inst)
            (@HSub.hSub.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
              (@instHSub.{max p2m_u_0 p2m_u_1}
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (@Matrix.sub.{p2m_u_0, p2m_u_1, p2m_u_1} n n
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (@Polynomial.instSub.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))
              (@OfNat.ofNat.{max p2m_u_0 p2m_u_1}
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (nat_lit 1)
                (@One.toOfNat1.{max p2m_u_0 p2m_u_1}
                  (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                  (@Matrix.one.{p2m_u_0, p2m_u_1} n
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    inst_2
                    (@Polynomial.instZero.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.instOne.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
              (@HSMul.hSMul.{p2m_u_0, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                (@instHSMul.{p2m_u_0, max p2m_u_0 p2m_u_1}
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
                  (@Matrix.smul.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_0} n n
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@Polynomial.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                    (@instSMulOfMul.{p2m_u_0}
                      (@Polynomial.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                      (@Polynomial.instMul.{p2m_u_0} R
                        (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
                (@Polynomial.X.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} n n R
                  (@Polynomial.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                  M
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
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))))))) := @_root_.Matrix.p2m_local_derivative_det_one_sub_X_smul

