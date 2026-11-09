-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_squareFibre_union_at_most_two_orbits
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:02.72522+00:00
-- url     : https://prove2.me/submissions/93f73bcf-36f5-4380-818f-1ddec7fcd259

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_distinct_doubles_no_exception
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_same_doubles_no_exception
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58

set_option autoImplicit false

/-!
RECOH conditional bank: bridge to the STROBO orbit decomposition.
DRAFT: not compiled. This theorem reuses existing STROBO classification.
Clean branch based on main; independently compile with Lean 4.29.1.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Each triple fibre is a union of at most two two-torsion translation orbits.
This is a bridge lemma, not a fresh classification of additive collisions. -/
theorem p2m_local_recoh_squareFibre_union_at_most_two_orbits
    (S : Finset G) (hS : S.card = 3) :
    ∃ T : Finset G,
      squareFibre S = torsionOrbit S ∪ torsionOrbit T := by
  classical
  rcases card_three_doubling_shapes S hS with
    ⟨a, b, c, hs, hab, hac, hbc⟩ |
    ⟨a, b, c, hs, hab, hac⟩ |
    ⟨a, b, d, hd, hd0, hab, hs⟩
  · refine ⟨S, ?_⟩
    rw [squareFibre_eq_orbit_of_no_exception S hS
      (distinct_doubles_no_exception S hS a b c hs hab hac hbc)]
    simp
  · refine ⟨S, ?_⟩
    rw [squareFibre_eq_orbit_of_no_exception S hS
      (same_doubles_no_exception S hS a b c hs hab hac)]
    simp
  · let R : Finset G := {a, b + b - a, (b + b - a) + d}
    by_cases h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
        ((b - a) + (b - a)) + (b - a) = d
    · refine ⟨R, ?_⟩
      rw [hs, paired_squareFibre_eq a b d hd hd0 hab, if_pos h3]
    · refine ⟨S, ?_⟩
      rw [hs, paired_squareFibre_eq a b d hd hd0 hab, if_neg h3]
      simp


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun T =>
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)
        (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
          (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
          (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 T)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_squareFibre_union_at_most_two_orbits

