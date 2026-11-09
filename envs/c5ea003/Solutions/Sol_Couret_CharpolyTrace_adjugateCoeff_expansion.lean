-- Prove2me | solution 1 for Couret.CharpolyTrace.adjugateCoeff_expansion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:18.618693+00:00
-- url     : https://prove2.me/submissions/6ce6e17b-b2b2-4e4e-9b36-1f0f352b7788

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







theorem matPolyEquiv_reverseCharmatrix (A : Matrix i i R) :
    matPolyEquiv (reverseCharmatrix A) = 1 - X * C A := by
  simp [reverseCharmatrix]

theorem reverseCharmatrix_mul_adjugate (A : Matrix i i R) :
    (1 - X * C A) * matPolyEquiv (reverseCharmatrix A).adjugate =
      A.charpolyRev.map (algebraMap R (Matrix i i R)) := by
  have h := congrArg matPolyEquiv (Matrix.mul_adjugate (reverseCharmatrix A))
  rw [map_mul, matPolyEquiv_reverseCharmatrix, matPolyEquiv_smul_one] at h
  exact h

theorem adjugateCoeff_zero (A : Matrix i i R) : adjugateCoeff A 0 = 1 := by
  have hp0 : A.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have h := congrArg (fun p : (Matrix i i R)[X] => p.coeff 0)
    (reverseCharmatrix_mul_adjugate A)
  simpa [sub_mul, mul_assoc, adjugateCoeff, hp0] using h

theorem adjugateCoeff_succ (A : Matrix i i R) (k : ℕ) :
    adjugateCoeff A (k + 1) =
      A * adjugateCoeff A k + A.charpolyRev.coeff (k + 1) • (1 : Matrix i i R) := by
  have h := congrArg (fun p : (Matrix i i R)[X] => p.coeff (k + 1))
    (reverseCharmatrix_mul_adjugate A)
  simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_X_mul, coeff_C_mul,
    coeff_map, Algebra.algebraMap_eq_smul_one] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem p2m_local_adjugateCoeff_expansion (A : Matrix i i R) (k : ℕ) :
    adjugateCoeff A k = A ^ k +
      ∑ j ∈ Finset.range k,
        A.charpolyRev.coeff (j + 1) • A ^ (k - (j + 1)) := by
  induction k with
  | zero => simp [adjugateCoeff_zero]
  | succ k ih =>
      rw [adjugateCoeff_succ, ih, mul_add, Finset.mul_sum,
        ← pow_succ', Finset.sum_range_succ]
      have hsum :
          (∑ j ∈ Finset.range k,
              A * (A.charpolyRev.coeff (j + 1) • A ^ (k - (j + 1)))) =
            ∑ j ∈ Finset.range k,
              A.charpolyRev.coeff (j + 1) • A ^ (k + 1 - (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < k := Finset.mem_range.mp hj
        have he : k + 1 - (j + 1) = (k - (j + 1)) + 1 := by omega
        rw [mul_smul_comm, ← pow_succ', he]
      rw [hsum]
      simp only [Nat.sub_self, pow_zero]
      abel









end Couret.CharpolyTrace



universe p2m_u_0 p2m_u_1
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] {i : Type p2m_u_1} [inst_1 : Fintype.{p2m_u_1} i]
  [inst_2 : DecidableEq.{p2m_u_1 + 1} i] (A : Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) (k : Nat),
  @Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
    (@Couret.CharpolyTrace.adjugateCoeff.{p2m_u_0, p2m_u_1} R inst i inst_1 inst_2 A k)
    (@HAdd.hAdd.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1}
      (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
      (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
      (@instHAdd.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
        (@Matrix.add.{p2m_u_0, p2m_u_1, p2m_u_1} i i R
          (@Distrib.toAdd.{p2m_u_0} R
            (@instDistribOfSemiring.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))))))
      (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
        (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
        (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
          (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
              (@Matrix.semiring.{p2m_u_0, p2m_u_1} i R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1 inst_2))))
        A k)
      (@Finset.sum.{0, max p2m_u_0 p2m_u_1} Nat (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
        (@Matrix.addCommMonoid.{p2m_u_0, p2m_u_1, p2m_u_1} i i R
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} R
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{p2m_u_0} R
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{p2m_u_0} R
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{p2m_u_0} R
                  (@CommRing.toNonUnitalCommRing.{p2m_u_0} R inst))))))
        (Finset.range k) fun j =>
        @HSMul.hSMul.{p2m_u_0, max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} R (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
          (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
          (@instHSMul.{p2m_u_0, max p2m_u_0 p2m_u_1} R (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@Matrix.smul.{p2m_u_0, p2m_u_1, p2m_u_1, p2m_u_0} i i R R
              (@instSMulOfMul.{p2m_u_0} R
                (@Distrib.toMul.{p2m_u_0} R
                  (@instDistribOfSemiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))))
          (@Polynomial.coeff.{p2m_u_0} R
            (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst))
            (@Matrix.charpolyRev.{p2m_u_0, p2m_u_1} R inst i inst_2 inst_1 A)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
            (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
            (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R) Nat
              (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_1, p2m_u_1, p2m_u_0} i i R)
                  (@Matrix.semiring.{p2m_u_0, p2m_u_1} i R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)) inst_1 inst_2))))
            A
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := @_root_.Couret.CharpolyTrace.p2m_local_adjugateCoeff_expansion

