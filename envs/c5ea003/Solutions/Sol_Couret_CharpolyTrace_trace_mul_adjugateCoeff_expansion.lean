-- Prove2me | solution 1 for Couret.CharpolyTrace.trace_mul_adjugateCoeff_expansion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:19.325195+00:00
-- url     : https://prove2.me/submissions/9ba72b10-d351-43b4-9731-0b3dbf957ce0

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CharpolyTrace_adjugateCoeff_expansion
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

















theorem p2m_local_trace_mul_adjugateCoeff_expansion (A : Matrix i i R) (k : ℕ) :
    Matrix.trace (A * adjugateCoeff A k) = Matrix.trace (A ^ (k + 1)) +
      ∑ j ∈ Finset.range k,
        A.charpolyRev.coeff (j + 1) * Matrix.trace (A ^ (k + 1 - (j + 1))) := by
  rw [adjugateCoeff_expansion, mul_add, Finset.mul_sum, Matrix.trace_add,
    Matrix.trace_sum, ← pow_succ']
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  have he : k + 1 - (j + 1) = (k - (j + 1)) + 1 := by omega
  rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, ← pow_succ', he]







end Couret.CharpolyTrace



universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] {i : Type p2m_u_1} [inst_1 : Fintype.{p2m_u_1} i]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} i] (A : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) (k : Nat),
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
    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
      (@instHAdd.{p2m_u_0} R
        (@Distrib.toAdd.{p2m_u_0} R
          (@instDistribOfSemiring.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
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
          A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Finset.sum.{0, p2m_u_0} Nat R
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst)))))
        (Finset.range k) fun j =>
        @HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
          (@instHMul.{p2m_u_0} R
            (@Distrib.toMul.{p2m_u_0} R
              (@instDistribOfSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@Polynomial.coeff.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@Matrix.charpolyRev.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
              A
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) := @_root_.Couret.CharpolyTrace.p2m_local_trace_mul_adjugateCoeff_expansion

