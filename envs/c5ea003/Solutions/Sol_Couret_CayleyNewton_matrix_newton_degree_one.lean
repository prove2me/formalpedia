-- Prove2me | solution 1 for Couret.CayleyNewton.matrix_newton_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:02.689193+00:00
-- url     : https://prove2.me/submissions/dff575ba-5996-43e1-9360-990ecf9479e9

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

/-- Newton's first equation holds for every square rational matrix,
including a matrix indexed by an empty type. Unlike the existing
conditional higher-degree theorems, this requires no extra premises. -/
theorem p2m_local_matrix_newton_degree_one
    {i : Type*} [Fintype i] [DecidableEq i]
    (A : Matrix i i ℚ) :
    NewtonTraceEquation (reverseCharpolyCoeff A)
      (fun m => Matrix.trace (A ^ m)) 1 := by
  classical
  by_cases hzero : Fintype.card i = 0
  · haveI : IsEmpty i := Fintype.card_eq_zero_iff.mp hzero
    simp [NewtonTraceEquation, reverseCharpolyCoeff, hzero, Matrix.trace]
  · haveI : Nonempty i := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
    have hone : 1 ≤ Fintype.card i := by omega
    simp only [NewtonTraceEquation, Nat.sub_self, Finset.range_zero,
      Finset.sum_empty, add_zero, pow_one, Nat.cast_one, one_mul]
    rw [reverseCharpolyCoeff, if_pos hone,
      Matrix.trace_eq_neg_charpoly_coeff A]
    ring

end Couret.CayleyNewton


universe p2m_u_0
theorem solution : ∀ {i : Type p2m_u_0} [inst : Fintype.{p2m_u_0} i] [inst_1 : DecidableEq.{p2m_u_0 + 1} i]
  (A : Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat),
  Couret.CayleyNewton.NewtonTraceEquation (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 A)
    (fun m =>
      @Matrix.trace.{p2m_u_0, 0} i Rat inst Rat.addCommMonoid
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
          (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
          (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
            (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
              (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                (@Matrix.semiring.{0, p2m_u_0} i Rat Rat.semiring inst inst_1))))
          A m))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.CayleyNewton.p2m_local_matrix_newton_degree_one

