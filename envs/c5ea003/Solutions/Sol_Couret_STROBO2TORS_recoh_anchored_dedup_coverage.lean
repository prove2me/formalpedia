-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_anchored_dedup_coverage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:58.096193+00:00
-- url     : https://prove2.me/submissions/b9ec8ed9-d76f-4100-adce-f38d05cb753c

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_mem_source
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_orbit_check_iff
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

















/-- Deduplication preserves exactly the supports represented up to H-translation. -/
theorem p2m_local_recoh_anchored_dedup_coverage (anchor : Finset G → G)
    (xs : List (Finset G)) (hanchor : ∀ B ∈ xs, anchor B ∈ B)
    (S : Finset G) :
    (∃ B ∈ recohAnchoredOrbitDedup anchor xs, OrdinaryPartner B S) ↔
      ∃ B ∈ xs, OrdinaryPartner B S := by
  constructor
  · rintro ⟨B, hB, hBS⟩
    exact ⟨B, recoh_anchored_dedup_mem_source anchor xs B hB, hBS⟩
  · intro h
    induction xs with
    | nil => simp at h
    | cons B xs ih =>
      have hb : anchor B ∈ B := hanchor B List.mem_cons_self
      have ht : ∀ C ∈ xs, anchor C ∈ C :=
        fun C hC => hanchor C (List.mem_cons_of_mem B hC)
      simp only [recohAnchoredOrbitDedup]
      split_ifs with hseen
      · rcases h with ⟨C, hC, hCS⟩
        rcases List.mem_cons.mp hC with rfl | hC
        · obtain ⟨D, hD, hBD⟩ := List.any_eq_true.mp hseen
          have hBD' := (recoh_anchored_orbit_check_iff (anchor C) C D hb).mp hBD
          exact ⟨D, hD, recoh_ordinary_partner_trans
            (recoh_ordinary_partner_symm hBD') hCS⟩
        · exact ih ht ⟨C, hC, hCS⟩
      · rcases h with ⟨C, hC, hCS⟩
        rcases List.mem_cons.mp hC with rfl | hC
        · exact ⟨C, List.mem_cons_self, hCS⟩
        · obtain ⟨D, hD, hDS⟩ := ih ht ⟨C, hC, hCS⟩
          exact ⟨D, List.mem_cons_of_mem B hD, hDS⟩









section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (anchor : Finset.{p2m_u_0} G → G) (xs : List.{p2m_u_0} (Finset.{p2m_u_0} G)),
  (∀ (B : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G)) xs B →
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) B
          (anchor B)) →
    ∀ (S : Finset.{p2m_u_0} G),
      Iff
        (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
          And
            (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Couret.STROBO2TORS.recohAnchoredOrbitDedup.{p2m_u_0} G inst inst_1 anchor xs) B)
            (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B S))
        (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
          And
            (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G)) xs B)
            (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_anchored_dedup_coverage

