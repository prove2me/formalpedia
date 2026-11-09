-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_bank_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:23.489785+00:00
-- url     : https://prove2.me/submissions/b84895c5-2d7d-4f3f-8bdc-ab6c1b9b1bff

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









/-- The requested bank has all binary slots and either zero or one ternary
slot. This holds even for arbitrary square input. -/
theorem p2m_local_recoh_selected_bank_card
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Fintype.card (RecohSelectedBankIndex q entries) =
      Fintype.card (RecohEvenCoordinate q) +
        if recohSquareTernaryChoice q entries = none then 0 else 1 := by
  rw [Fintype.card_sum]
  congr 1
  by_cases hnone : recohSquareTernaryChoice q entries = none
  · rw [if_pos hnone]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun a => ?_⟩
    exact (Option.some_ne_none a.val) (a.property.symm.trans hnone)
  · rw [if_neg hnone]
    obtain ⟨j, hchoice⟩ := Option.ne_none_iff_exists'.mp hnone
    exact Fintype.card_eq_one_iff.mpr ⟨⟨j, hchoice⟩, fun a => Subsingleton.elim _ _⟩



















































end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)),
  @Eq.{1} Nat
    (@Fintype.card.{0} (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
      (@instFintypeSum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
        (@Couret.STROBO2TORS.RecohSelectedTernaryIndex d q inst entries)
        (@Subtype.fintype.{0} (Fin d)
          (fun i => @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
          (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
          (Fin.fintype d))
        (@Couret.STROBO2TORS.recohSelectedTernaryFintype d q inst entries)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Fintype.card.{0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
        (@Subtype.fintype.{0} (Fin d)
          (fun i => @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
          (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
          (Fin.fintype d)))
      (@ite.{1} Nat
        (@Eq.{1}
          (Option.{0}
            (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
          (@Option.none.{0}
            (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
        (@Option.decidableEqNone.{0}
          (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_bank_card

