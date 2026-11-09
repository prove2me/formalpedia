-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_eq_translate_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:19.82531+00:00
-- url     : https://prove2.me/submissions/8423d5fa-d678-46b0-aef2-a451ee145593

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Translation and incidence transfer from unrestricted collision pairs to pairs
whose two supports avoid zero. The incidence argument does not assume that
translation acts freely. This module adds to the historical certificates.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















/-- Arbitrary translations shift the argument of the ordered square by 2a. -/
theorem orderedSquare_translate_covariant (S : Finset G) (a z : G) :
    orderedSquare (translateSupport S a) (z + (a + a)) = orderedSquare S z := by
  unfold orderedSquare translateSupport
  rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
  apply Finset.sum_congr rfl
  intro y hy
  have hsum : (x + a) + (y + a) = (x + y) + (a + a) := by abel
  simp only [hsum, add_left_inj]

theorem p2m_local_orderedSquare_eq_translate_iff (S T : Finset G) (a : G) :
    (∀ z : G, orderedSquare (translateSupport S a) z =
      orderedSquare (translateSupport T a) z) ↔
    (∀ z : G, orderedSquare S z = orderedSquare T z) := by
  constructor
  · intro h z
    simpa only [orderedSquare_translate_covariant] using h (z + (a + a))
  · intro h z
    have hz : (z - (a + a)) + (a + a) = z := by abel
    simpa only [hz, orderedSquare_translate_covariant] using
      (orderedSquare_translate_covariant S a (z - (a + a))).trans
        ((h (z - (a + a))).trans
          (orderedSquare_translate_covariant T a (z - (a + a))).symm)

section Finite

variable [Fintype G]


























end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (S T : Finset.{p2m_u_0} G)
  (a : G),
  Iff
    (∀ (z : G),
      @Eq.{1} Nat
        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
          (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S a) z)
        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
          (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T a) z))
    (∀ (z : G),
      @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z)) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_eq_translate_iff

