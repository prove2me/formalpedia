-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_bank_card_eq_fibre_budget
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:27.89383+00:00
-- url     : https://prove2.me/submissions/2af3bfc6-065c-4f0a-b598-046b0b0a8845

import Aesop
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_product_torsion_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_exceptional
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_ordinary
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_ternary_choice_none_iff
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497

set_option autoImplicit false

/-!
The typed coefficient decoder with all binary coordinates and at most one
ternary coordinate selected from the labelled square. The square selector
runs before observed character coefficients are supplied. Its exact integer
backend retains the previously certified half-sum and sign-recovery code.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]













/-- The executable selection attains the exact information budget of its
entire square fibre. -/
theorem p2m_local_recoh_selected_bank_card_eq_fibre_budget
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    Fintype.card (RecohSelectedBankIndex q entries) = recohFibreBudget S := by
  rw [recoh_selected_bank_card]
  rcases squareFibre_card_h_or_two_h S hS with ho | he
  · rw [if_pos ((recoh_square_ternary_choice_none_iff q entries S hS hsquare).mpr ho),
      Nat.add_zero, recoh_fibre_budget_ordinary
        (Fintype.card (RecohEvenCoordinate q)) (recoh_cyclic_product_torsion_card q 2) S ho]
  · have hne : (squareFibre S).card ≠
        (twoTorsion : Finset ((i : Fin d) → ZMod (q i))).card := by
      have hp := twoTorsion_card_pos (G := (i : Fin d) → ZMod (q i))
      omega
    rw [if_neg (fun hn => hne
      ((recoh_square_ternary_choice_none_iff q entries S hS hsquare).mp hn)),
      recoh_fibre_budget_exceptional (Fintype.card (RecohEvenCoordinate q))
        (recoh_cyclic_product_torsion_card q 2) S he]















































end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
        (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          S)
        (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          entries) →
      @Eq.{1} Nat
        (@Fintype.card.{0} (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
          (@instFintypeSum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
            (@Couret.STROBO2TORS.RecohSelectedTernaryIndex d q inst entries)
            (@Subtype.fintype.{0} (Fin d)
              (fun i =>
                @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
              (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
              (Fin.fintype d))
            (@Couret.STROBO2TORS.recohSelectedTernaryFintype d q inst entries)))
        (@Couret.STROBO2TORS.recohFibreBudget.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
            @ZMod.fintype (q a) (inst a))
          S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_bank_card_eq_fibre_budget

