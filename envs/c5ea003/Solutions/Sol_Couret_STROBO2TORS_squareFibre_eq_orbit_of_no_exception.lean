-- Prove2me | solution 1 for Couret.STROBO2TORS.squareFibre_eq_orbit_of_no_exception
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:54.915953+00:00
-- url     : https://prove2.me/submissions/4a7f0375-b47a-4b3a-8a4b-33721049d2ef

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]





















theorem p2m_local_squareFibre_eq_orbit_of_no_exception (S : Finset G) (hS : S.card = 3)
    (hne : ∀ T : Finset G, ¬ ExceptionalPartner S T) :
    squareFibre S = torsionOrbit S := by
  apply Finset.Subset.antisymm
  · intro T ht
    obtain ⟨ht3, hsq⟩ := (mem_squareFibre S T).mp ht
    rcases orderedSquare_classification_necessary S T hS ht3 hsq with h | h
    · exact (mem_torsionOrbit S T).mpr h
    · exact (hne T h).elim
  · exact torsionOrbit_subset_fibre S hS




























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
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    (∀ (T : Finset.{p2m_u_0} G), Not (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T)) →
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S) := @_root_.Couret.STROBO2TORS.p2m_local_squareFibre_eq_orbit_of_no_exception

