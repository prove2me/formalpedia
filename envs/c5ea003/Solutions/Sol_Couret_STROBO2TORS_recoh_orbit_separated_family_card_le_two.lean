-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_orbit_separated_family_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:47.638733+00:00
-- url     : https://prove2.me/submissions/4044a85c-cd9b-453c-90ee-00cec9b0ee16

import Aesop
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_le_two_h
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- A family of correct, pairwise distinct H-orbits in a triple fibre has
at most two members. Nonemptiness supplies its own reference realization. -/
theorem p2m_local_recoh_orbit_separated_family_card_le_two
    (R : G → ℕ) (P : Finset (Finset G))
    (hsound : ∀ B ∈ P, B.card = 3 ∧ orderedSquare B = R)
    (hsep : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → ¬ OrdinaryPartner B C) :
    P.card ≤ 2 := by
  classical
  by_cases hempty : P = ∅
  · simp [hempty]
  obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hdisj : (P : Set (Finset G)).PairwiseDisjoint torsionOrbit := by
    intro B hB C hC hBC
    exact torsionOrbits_disjoint B C (hsep B hB C hC hBC)
  have hsub : P.biUnion torsionOrbit ⊆ squareFibre S := by
    intro T hT
    obtain ⟨B, hB, hBT⟩ := Finset.mem_biUnion.mp hT
    obtain ⟨hTcard, hTR⟩ := recoh_realization_of_ordinary_partner R B T
      (hsound B hB).1 (hsound B hB).2 ((mem_torsionOrbit B T).mp hBT)
    exact (mem_squareFibre S T).mpr
      ⟨hTcard, fun z => (congrFun (hsound S hS).2 z).trans (congrFun hTR z).symm⟩
  have hcard : (P.biUnion torsionOrbit).card = P.card * (twoTorsion : Finset G).card := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ B ∈ P, (torsionOrbit B).card = ∑ _B ∈ P, (twoTorsion : Finset G).card := by
        apply Finset.sum_congr rfl
        intro B hB
        exact torsionOrbit_card B (hsound B hB).1
      _ = P.card * (twoTorsion : Finset G).card := by simp
  have hmul : P.card * (twoTorsion : Finset G).card ≤
      2 * (twoTorsion : Finset G).card := by
    rw [← hcard]
    exact (Finset.card_le_card hsub).trans (squareFibre_card_le_two_h S (hsound S hS).1)
  exact Nat.le_of_mul_le_mul_right hmul twoTorsion_card_pos









section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





















end CyclicSelected

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (R : G → Nat) (P : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  (∀ (B : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          P B →
        And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Eq.{p2m_u_0 + 1} (G → Nat) (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 B) R)) →
    (∀ (B : Finset.{p2m_u_0} G),
        @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
            P B →
          ∀ (C : Finset.{p2m_u_0} G),
            @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                  (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                P C →
              @Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) B C →
                Not (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B C)) →
      @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) P)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_orbit_separated_family_card_le_two

