-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_dedup_ternary_choice_eq_legacy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:56:12.727748+00:00
-- url     : https://prove2.me/submissions/df8c9da4-b73e-41c2-8f5a-395cc2699fbd

import Aesop
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_cover
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_orbit_families_eq_legacy
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c

set_option autoImplicit false

/-!
Transport of the conditional ternary selector to the parity representatives.

A ternary observation is constant on each two-torsion orbit. Consequently
both the one-orbit predicate and every separating-coordinate predicate
depend only on the finite family of orbits. Scanning the same coordinate
order therefore returns exactly the same first coordinate, even when the
representatives or their deduplication order differ.

The definitions below concern typed mathematical inputs. They do not
identify Python list order, parsing, exceptions, or execution semantics.
-/

namespace Couret.STROBO2TORS

section FiniteFamilies

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







end FiniteFamilies

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



























/-- The same first coordinate is selected after any valid enumeration and
the proved right-fold deduplication, regardless of representative retention. -/
theorem p2m_local_recoh_parity_dedup_ternary_choice_eq_legacy
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    recohTernaryChoiceFromRepresentatives q (recohAnchoredOrbitDedup anchor xs).toFinset =
      recohSquareTernaryChoice q entries := by
  have hcover := recoh_parity_dedup_cover
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q) (recoh_product_half_spec q)
    (recoh_selected_square_support_covered q entries) xs hxs anchor hanchor
  have hnonempty : ∀ B ∈ (recohAnchoredOrbitDedup anchor xs).toFinset, B.Nonempty := by
    intro B hB
    apply Finset.card_pos.mp
    rw [(hcover.1 B hB).1]
    decide
  change recohTernaryChoiceFromRepresentatives q (recohAnchoredOrbitDedup anchor xs).toFinset =
    recohTernaryChoiceFromRepresentatives q (recohCyclicSquareRepresentatives q entries)
  apply recoh_ternary_choice_eq_of_orbit_families_eq q _ _ hnonempty
    (recoh_cyclic_square_representatives_nonempty q entries)
  exact recoh_parity_dedup_orbit_families_eq_legacy
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q) (recoh_product_half_spec q)
    (recoh_selected_square_support_covered q entries) xs hxs anchor hanchor

end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (xs : List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))),
  @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@List.toFinset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (fun a b =>
          @Finset.decidableEq.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            a b)
        xs)
      (@Couret.STROBO2TORS.recohCyclicParityRepresentatives d q entries) →
    ∀ (anchor : Finset.{0} ((i : Fin d) → ZMod (q i)) → (i : Fin d) → ZMod (q i)),
      (∀ (B : Finset.{0} ((i : Fin d) → ZMod (q i))),
          @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (@List.instMembership.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) xs B →
            @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i)) (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (@SetLike.instMembership.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) ((i : Fin d) → ZMod (q i))
                (@Finset.instSetLike.{0} ((i : Fin d) → ZMod (q i))))
              B (anchor B)) →
        @Eq.{1}
          (Option.{0}
            (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Couret.STROBO2TORS.recohTernaryChoiceFromRepresentatives d q inst
            (@List.toFinset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (fun a b =>
                @Finset.decidableEq.{0} ((i : Fin d) → ZMod (q i))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  a b)
              (@Couret.STROBO2TORS.recohAnchoredOrbitDedup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                (fun a b =>
                  @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                    (Fin.fintype d) a b)
                anchor xs)))
          (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_dedup_ternary_choice_eq_legacy

