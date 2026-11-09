-- Prove2me | solution 1 for Couret.STROBO2TORS.translateSupport_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:25.480412+00:00
-- url     : https://prove2.me/submissions/69450eee-7a24-4f7c-950b-eab69e0f7378

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













theorem p2m_local_translateSupport_injective (a : G) :
    Function.Injective (fun S : Finset G => translateSupport S a) := by
  intro S T h
  have := congrArg (fun U => translateSupport U (-a)) h
  simpa using this





section Finite

variable [Fintype G]


























end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a : G),
  @Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) fun S =>
    @Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S a := @_root_.Couret.STROBO2TORS.p2m_local_translateSupport_injective

