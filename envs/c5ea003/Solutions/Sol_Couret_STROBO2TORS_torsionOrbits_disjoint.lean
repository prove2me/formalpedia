-- Prove2me | solution 1 for Couret.STROBO2TORS.torsionOrbits_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:00.850818+00:00
-- url     : https://prove2.me/submissions/a1591399-6e7c-425c-906b-bd588b56ebde

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]























theorem p2m_local_torsionOrbits_disjoint (S R : Finset G) (hne : ¬ OrdinaryPartner S R) :
    Disjoint (torsionOrbit S) (torsionOrbit R) := by
  apply Finset.disjoint_left.mpr
  intro T hTS hTR
  obtain ⟨u, hu, hSu⟩ := (mem_torsionOrbit S T).mp hTS
  obtain ⟨v, hv, hRv⟩ := (mem_torsionOrbit R T).mp hTR
  have huv : (u + v) + (u + v) = 0 := by
    calc
      (u + v) + (u + v) = (u + u) + (v + v) := by abel
      _ = 0 := by simp [hu, hv]
  have hh : translateSupport S (u + v) = R := by
    calc
      translateSupport S (u + v) = translateSupport (translateSupport S u) v :=
        (translateSupport_add S u v).symm
      _ = translateSupport (translateSupport R v) v := by rw [← hSu, hRv]
      _ = R := translateSupport_twice R v hv
  exact hne ⟨u + v, huv, hh.symm⟩


























/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S R : Finset.{p2m_u_0} G),
  Not (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S R) →
    @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.partialOrder.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instOrderBot.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
      (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 R) := @_root_.Couret.STROBO2TORS.p2m_local_torsionOrbits_disjoint

