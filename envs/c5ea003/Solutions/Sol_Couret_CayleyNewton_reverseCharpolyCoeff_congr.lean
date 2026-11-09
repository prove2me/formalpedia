-- Prove2me | solution 1 for Couret.CayleyNewton.reverseCharpolyCoeff_congr
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:19:19.693889+00:00
-- url     : https://prove2.me/submissions/6437f4e0-b9ad-4e32-b78d-41a33e042a0b

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



theorem p2m_local_reverseCharpolyCoeff_congr
    {i : Type*} [Fintype i] [DecidableEq i]
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly) :
    reverseCharpolyCoeff A = reverseCharpolyCoeff B := by
  funext k
  by_cases hk : k ≤ Fintype.card i
  · simp only [reverseCharpolyCoeff, if_pos hk, hp]
  · simp only [reverseCharpolyCoeff, if_neg hk]

























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
    @Eq.{1} (Nat → Rat) (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 A)
      (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} i inst inst_1 B) := @_root_.Couret.CayleyNewton.p2m_local_reverseCharpolyCoeff_congr

