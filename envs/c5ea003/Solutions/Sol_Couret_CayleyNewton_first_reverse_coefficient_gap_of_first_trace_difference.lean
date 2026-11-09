-- Prove2me | solution 1 for Couret.CayleyNewton.first_reverse_coefficient_gap_of_first_trace_difference
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:21.647407+00:00
-- url     : https://prove2.me/submissions/cbca16f4-9db4-4aff-880f-6ed8abe8abbc

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyNewton_newton_coefficient_prefix_eq
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_newton_first_gap_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20 — exact first characteristic coefficient obstruction.

RESEARCH CANDIDATE: must be compiled with the pinned Lean 4.29.1
toolchain and its #print axioms checked before a certification claim.

The general matrix theorem uses the now-proposed unconditional Newton
recurrence for rational square matrices. The directed Cayley corollary
uses the previously established first trace discrepancy at one third
of the odd quotient cardinality. No graph symmetry, loop exclusion,
new axiom, or independent generation assumption is introduced.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNewton

variable {i : Type*} [Fintype i] [DecidableEq i]

/-- Equality of every smaller positive trace, followed by an actual
trace difference at degree k, produces the first differing reverse
characteristic coefficient, and also determines its signed difference
exactly. This uses the unconditional matrix Newton theorem, rather
than an assumption that A or B satisfies the recurrence. -/
theorem p2m_local_first_reverse_coefficient_gap_of_first_trace_difference
    (A B : Matrix i i ℚ) (k : ℕ) (hk : 0 < k)
    (hprev : ∀ j : ℕ, 0 < j → j < k →
      Matrix.trace (A ^ j) = Matrix.trace (B ^ j))
    (hdiff : Matrix.trace (A ^ k) ≠ Matrix.trace (B ^ k)) :
    (∀ j : ℕ, 0 < j → j < k →
        reverseCharpolyCoeff A j = reverseCharpolyCoeff B j) ∧
      reverseCharpolyCoeff A k ≠ reverseCharpolyCoeff B k ∧
      (k : ℚ) * (reverseCharpolyCoeff A k - reverseCharpolyCoeff B k) =
        -(Matrix.trace (A ^ k) - Matrix.trace (B ^ k)) := by
  have hA : ∀ j : ℕ, 0 < j → j ≤ k →
      NewtonTraceEquation (reverseCharpolyCoeff A)
        (fun m => Matrix.trace (A ^ m)) j := by
    intro j hj _
    exact satisfiesMatrixNewton A j hj
  have hB : ∀ j : ℕ, 0 < j → j ≤ k →
      NewtonTraceEquation (reverseCharpolyCoeff B)
        (fun m => Matrix.trace (B ^ m)) j := by
    intro j hj _
    exact satisfiesMatrixNewton B j hj
  refine ⟨?_, ?_, ?_⟩
  · exact newton_coefficient_prefix_eq
      (reverseCharpolyCoeff A) (reverseCharpolyCoeff B)
      (fun m => Matrix.trace (A ^ m))
      (fun m => Matrix.trace (B ^ m)) k
      (fun j hj hlt => hA j hj (Nat.le_of_lt hlt))
      (fun j hj hlt => hB j hj (Nat.le_of_lt hlt))
      hprev
  · exact newton_first_coefficient_ne_of_trace_prefix
      (reverseCharpolyCoeff A) (reverseCharpolyCoeff B)
      (fun m => Matrix.trace (A ^ m))
      (fun m => Matrix.trace (B ^ m))
      k hk hA hB hprev hdiff
  · exact newton_first_gap_of_trace_prefix
      (reverseCharpolyCoeff A) (reverseCharpolyCoeff B)
      (fun m => Matrix.trace (A ^ m))
      (fun m => Matrix.trace (B ^ m))
      k hk hA hB hprev

end Couret.CayleyNewton

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {i : Type p2m_u_0} [inst : Fintype.{p2m_u_0} i] [inst_1 : DecidableEq.{p2m_u_0 + 1} i]
  (A B : Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
          @LT.lt.{0} Nat instLTNat j k →
            @Eq.{1} Rat
              (@Matrix.trace.{p2m_u_0, 0} i Rat inst Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                        (@Matrix.semiring.{0, p2m_u_0} i Rat Rat.semiring inst inst_1))))
                  A j))
              (@Matrix.trace.{p2m_u_0, 0} i Rat inst Rat.addCommMonoid
                (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
                  (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                  (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat) Nat
                    (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                      (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} i i Rat)
                        (@Matrix.semiring.{0, p2m_u_0} i Rat Rat.semiring inst inst_1))))
                  B j))) →
      @Ne.{1} Rat
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
              B k)) →
        And
          (∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
              @LT.lt.{0} Nat instLTNat j k →
                @Eq.{1} Rat (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 A j)
                  (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 B j))
          (And
            (@Ne.{1} Rat (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 A k)
              (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 B k))
            (@Eq.{1} Rat
              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Nat.cast.{0} Rat Rat.instNatCast k)
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                  (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 A k)
                  (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 B k)))
              (@Neg.neg.{0} Rat Rat.instNeg
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
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
                      B k)))))) := @_root_.Couret.CayleyNewton.p2m_local_first_reverse_coefficient_gap_of_first_trace_difference

