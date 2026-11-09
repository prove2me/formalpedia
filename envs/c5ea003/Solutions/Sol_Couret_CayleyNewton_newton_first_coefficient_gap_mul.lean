-- Prove2me | solution 1 for Couret.CayleyNewton.newton_first_coefficient_gap_mul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:07.385216+00:00
-- url     : https://prove2.me/submissions/251aa726-2e0e-4114-a47a-80eaf1101018

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
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













/-- The first coefficient where two monic characteristic-polynomial
coefficient lists may differ is controlled by the corresponding power trace.

Unlike the cospectrality contradiction above, this lemma does NOT assume
equality of characteristic polynomials or even equality of the kth
coefficients. It determines their exact signed gap from a single pair
of Newton identities plus equality at all smaller positive indices. -/
theorem p2m_local_newton_first_coefficient_gap_mul
    (c d u v : ℕ → ℚ) (k : ℕ) (hk : 0 < k)
    (hcoeff : ∀ j : ℕ, 0 < j → j < k → c j = d j)
    (htrace : ∀ j : ℕ, 0 < j → j < k → u j = v j)
    (hu : NewtonTraceEquation c u k)
    (hv : NewtonTraceEquation d v k) :
    (k : ℚ) * (c k - d k) = -(u k - v k) := by
  unfold NewtonTraceEquation at hu hv
  have hsum :
      (∑ j ∈ Finset.range (k - 1), c (j + 1) * u (k - (j + 1))) =
        (∑ j ∈ Finset.range (k - 1), d (j + 1) * v (k - (j + 1))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < k - 1 := Finset.mem_range.mp hj
    have hjpos : 0 < j + 1 := by omega
    have hjupper : j + 1 < k := by omega
    have hpos : 0 < k - (j + 1) := by omega
    have hlt : k - (j + 1) < k := by omega
    rw [hcoeff (j + 1) hjpos hjupper,
      htrace (k - (j + 1)) hpos hlt]
  rw [hsum] at hu
  calc
    (k : ℚ) * (c k - d k) =
        (k : ℚ) * c k - (k : ℚ) * d k := by ring
    _ = -(u k - v k) := by linarith















end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet



theorem solution : ∀ (c d u v : Nat → Rat) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
          @LT.lt.{0} Nat instLTNat j k → @Eq.{1} Rat (c j) (d j)) →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
            @LT.lt.{0} Nat instLTNat j k → @Eq.{1} Rat (u j) (v j)) →
        Couret.CayleyNewton.NewtonTraceEquation c u k →
          Couret.CayleyNewton.NewtonTraceEquation d v k →
            @Eq.{1} Rat
              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Nat.cast.{0} Rat Rat.instNatCast k)
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (c k) (d k)))
              (@Neg.neg.{0} Rat Rat.instNeg
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (u k) (v k))) := @_root_.Couret.CayleyNewton.p2m_local_newton_first_coefficient_gap_mul

