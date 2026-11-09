-- Prove2me | solution 1 for Couret.CayleyNewton.newton_first_coefficient_ne_of_trace_prefix
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:36.93419+00:00
-- url     : https://prove2.me/submissions/6833dc7a-07df-4e72-be41-9506994a0772

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyNewton_newton_first_gap_of_trace_prefix
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





















/-- A first trace disagreement therefore refutes equality of the
corresponding coefficient, using only the finite Newton prefix. -/
theorem p2m_local_newton_first_coefficient_ne_of_trace_prefix
    (c d u v : ℕ → ℚ) (ell : ℕ) (hell : 0 < ell)
    (hu : ∀ k : ℕ, 0 < k → k ≤ ell → NewtonTraceEquation c u k)
    (hv : ∀ k : ℕ, 0 < k → k ≤ ell → NewtonTraceEquation d v k)
    (htrace : ∀ k : ℕ, 0 < k → k < ell → u k = v k)
    (hdiff : u ell ≠ v ell) :
    c ell ≠ d ell := by
  intro hcoeff
  have hgap := newton_first_gap_of_trace_prefix c d u v ell
    hell hu hv htrace
  rw [hcoeff, sub_self, mul_zero] at hgap
  have hzero : u ell - v ell = 0 := by
    simpa only [neg_eq_zero] using hgap.symm
  exact hdiff (sub_eq_zero.mp hzero)







end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet



theorem solution : ∀ (c d u v : Nat → Rat) (ell : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell →
    (∀ (k : Nat),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
          @LE.le.{0} Nat instLENat k ell → Couret.CayleyNewton.NewtonTraceEquation c u k) →
      (∀ (k : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
            @LE.le.{0} Nat instLENat k ell → Couret.CayleyNewton.NewtonTraceEquation d v k) →
        (∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
              @LT.lt.{0} Nat instLTNat k ell → @Eq.{1} Rat (u k) (v k)) →
          @Ne.{1} Rat (u ell) (v ell) → @Ne.{1} Rat (c ell) (d ell) := @_root_.Couret.CayleyNewton.p2m_local_newton_first_coefficient_ne_of_trace_prefix

