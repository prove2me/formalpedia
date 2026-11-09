-- Prove2me | solution 1 for Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_of_newton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:31.564201+00:00
-- url     : https://prove2.me/submissions/cfa9f699-e3f8-4bae-b710-70a2da6221ee

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyNewton_newtonTraceEquation_unique_positive
import Theorems.Thm_Couret_CayleyNewton_reverseCharpolyCoeff_congr
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — rational Newton recurrence research bridge (18 October 2026).

UNCOMPILED PROOF CANDIDATE. Deliberately isolated from certified modules.

This is a substantive intermediate obligation: the all-powers trace
consequence is derived from two explicit, identical Newton recurrences,
NOT from an opaque hypothesis equating the traces. It still remains to
prove that the trace sequence of EVERY rational square matrix satisfies
this exact recurrence from its characteristic polynomial.

Neither the existence of a proof in Mathlib at the pinned commit nor a
Lean 4.29.1 compilation of this file is claimed here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Couret.CayleyNewton



























/-- Fully proved at the recurrence level, CONDITIONAL on the two
matrices individually satisfying the explicit Newton recurrence.
For k=0 both matrix powers equal the identity. -/
theorem p2m_local_trace_pow_eq_of_charpoly_eq_of_newton
    {i : Type*} [Fintype i] [DecidableEq i]
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly)
    (hA : SatisfiesMatrixNewton A) (hB : SatisfiesMatrixNewton B) :
    ∀ k : ℕ, Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hc : reverseCharpolyCoeff A = reverseCharpolyCoeff B :=
      reverseCharpolyCoeff_congr A B hp
    have hB' : ∀ m : ℕ, 0 < m →
        NewtonTraceEquation (reverseCharpolyCoeff A)
          (fun j => Matrix.trace (B ^ j)) m := by
      intro m hm
      rw [hc]
      exact hB m hm
    exact newtonTraceEquation_unique_positive
      (reverseCharpolyCoeff A)
      (fun j => Matrix.trace (A ^ j))
      (fun j => Matrix.trace (B ^ j))
      hA hB' k hkpos

end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet



universe p2m_u_0
theorem solution : ∀ {i : Type p2m_u_0} [inst : Fintype.{p2m_u_0} i] [inst_1 : DecidableEq.{p2m_u_0 + 1} i]
  (A B : Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat),
  @Eq.{1} (@Polynomial.{0} Rat (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing i inst_1 inst A)
      (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing i inst_1 inst B) →
    @Couret.CayleyNewton.SatisfiesMatrixNewton.{p2m_u_0} i inst inst_1 A →
      @Couret.CayleyNewton.SatisfiesMatrixNewton.{p2m_u_0} i inst inst_1 B →
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
                B k)) := @_root_.Couret.CayleyNewton.p2m_local_trace_pow_eq_of_charpoly_eq_of_newton

