-- Prove2me | solution 1 for Couret.STROBO2TORS.translateSupport_symmDiff_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:20.312217+00:00
-- url     : https://prove2.me/submissions/1a9965d8-de0f-4f96-9695-0a83c47ec332

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









theorem translateSupport_symmDiff (S T : Finset G) (a : G) :
    translateSupport (S ∆ T) a = translateSupport S a ∆ translateSupport T a := by
  exact Finset.image_symmDiff S T (fun _ _ h => add_right_cancel h)

theorem p2m_local_translateSupport_symmDiff_card (S T : Finset G) (a : G) :
    (translateSupport S a ∆ translateSupport T a).card = (S ∆ T).card := by
  rw [← translateSupport_symmDiff, translateSupport_card]







section Finite

variable [Fintype G]


























end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (S T : Finset.{p2m_u_0} G)
  (a : G),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} G
      (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
        (@Finset.instSDiff.{p2m_u_0} G inst_1) (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S a)
        (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T a)))
    (@Finset.card.{p2m_u_0} G
      (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
        (@Finset.instSDiff.{p2m_u_0} G inst_1) S T)) := @_root_.Couret.STROBO2TORS.p2m_local_translateSupport_symmDiff_card

