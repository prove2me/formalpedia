-- Prove2me | solution 1 for Matrix.derivative_det_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:08.977004+00:00
-- url     : https://prove2.me/submissions/e4b0150f-b9f3-48fa-841d-70654bf08785

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset Polynomial Matrix

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

private theorem det_apply_rows (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← det_transpose M, det_apply']
  rfl

theorem p2m_local_derivative_det_polynomial (M : Matrix n n R[X]) :
    derivative M.det = trace (M.map derivative * M.adjugate) := by
  have hrow : derivative M.det =
      ∑ i, (M.updateRow i (fun j => derivative (M i j))).det := by
    rw [det_apply_rows, derivative_sum]
    simp_rw [derivative_intCast_mul, derivative_prod_finset, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [det_apply_rows]
    apply Finset.sum_congr rfl
    intro σ hσ
    congr 1
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [Matrix.updateRow_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj)]
  rw [hrow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _






end Matrix

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} {n : Type p2m_u_1} [inst : CommRing.{p2m_u_0} R] [inst_1 : Fintype.{p2m_u_1} n]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} n]
  (M :
    Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
      (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))),
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
        (@Polynomial.commRing.{p2m_u_0} R inst) M))
    (@Matrix.trace.{p2m_u_1, p2m_u_0} n
      (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
      inst_1
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0}
        (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0}
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0}
            (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0}
              (@Polynomial.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
              (@CommRing.toNonUnitalCommRing.{p2m_u_0}
                (@Polynomial.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
                (@Polynomial.commRing.{p2m_u_0} R inst))))))
      (@HMul.hMul.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
        (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
        (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
        (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} n n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_1} n n n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          inst_1
          (@Polynomial.instMul.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
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
                    (@Polynomial.commRing.{p2m_u_0} R inst)))))))
        (@Matrix.map.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_1} n n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))) M
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
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
        (@Matrix.adjugate.{p2m_u_1, p2m_u_0} n
          (@Polynomial.{p2m_u_0} R (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))
          inst_2 inst_1 (@Polynomial.commRing.{p2m_u_0} R inst) M))) := @_root_.Matrix.p2m_local_derivative_det_polynomial

