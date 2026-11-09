-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_orbit_coverage_iff_realization
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:51.084034+00:00
-- url     : https://prove2.me/submissions/614eb705-c874-4f7e-b53c-f4af1655a335

import Aesop
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_realization_of_ordinary_partner
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false

/-!
An anchored orbit test and a finite-list deduplication invariant.

The orbit test fixes one point of the left support and examines only the
points of the right support. It therefore examines three differences when
the right support has cardinal three. No ambient-group search is used.

The list routine retains the last representative of each orbit. This is a
deliberate model at the quotient level, not an assertion that its order or
chosen representatives equal the Python routine's first-retention order.
The results below concern represented orbits and pairwise inequivalence.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

























/-- Soundness and completeness characterize the represented fibre itself. -/
theorem p2m_local_recoh_orbit_coverage_iff_realization
    (R : G → ℕ) (reps : Finset (Finset G))
    (hsound : ∀ B ∈ reps, B.card = 3 ∧ orderedSquare B = R)
    (hcomplete : ∀ S : Finset G, S.card = 3 → orderedSquare S = R →
      ∃ B ∈ reps, OrdinaryPartner B S) (S : Finset G) :
    (∃ B ∈ reps, OrdinaryPartner B S) ↔ S.card = 3 ∧ orderedSquare S = R := by
  constructor
  · rintro ⟨B, hB, hBS⟩
    obtain ⟨hcard, hsquare⟩ := hsound B hB
    exact recoh_realization_of_ordinary_partner R B S hcard hsquare hBS
  · rintro ⟨hcard, hsquare⟩
    exact hcomplete S hcard hsquare

section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (R : G → Nat)
  (reps : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  (∀ (B : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          reps B →
        And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Eq.{p2m_u_0 + 1} (G → Nat) (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 B) R)) →
    (∀ (S : Finset.{p2m_u_0} G),
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          @Eq.{p2m_u_0 + 1} (G → Nat) (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S) R →
            @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
              And
                (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                    (Finset.{p2m_u_0} G) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                  reps B)
                (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B S)) →
      ∀ (S : Finset.{p2m_u_0} G),
        Iff
          (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
            And
              (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                  (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                reps B)
              (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B S))
          (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@Eq.{p2m_u_0 + 1} (G → Nat) (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S) R)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_orbit_coverage_iff_realization

