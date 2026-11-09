-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_bank_minimal
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:01.050613+00:00
-- url     : https://prove2.me/submissions/f15bf707-be5e-4df7-8eda-95c48d3851df

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_fibre_bank_size
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_card_eq_fibre_budget
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

































/-- No shorter bank of arbitrary complex characters can separate the same
fibre as this concrete, executable selection. -/
theorem p2m_local_recoh_selected_bank_minimal
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries)
    (k : ℕ) (hk : k < Fintype.card (RecohSelectedBankIndex q entries))
    (bank : Fin k → AddChar ((i : Fin d) → ZMod (q i)) ℂ) :
    ¬ Set.InjOn (fun T : Finset ((i : Fin d) → ZMod (q i)) =>
      fun i => recohSupportProbe (bank i) T) (squareFibre S) := by
  rw [recoh_selected_bank_card_eq_fibre_budget q entries S hS hsquare] at hk
  exact (recoh_optimal_fibre_bank_size (Fintype.card (RecohEvenCoordinate q))
    (recoh_cyclic_product_torsion_card q 2) S hS).2 k hk bank



























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
      ∀ (k : Nat),
        @LT.lt.{0} Nat instLTNat k
            (@Fintype.card.{0} (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
              (@instFintypeSum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (@Couret.STROBO2TORS.RecohSelectedTernaryIndex d q inst entries)
                (@Subtype.fintype.{0} (Fin d)
                  (fun i =>
                    @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
                  (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
                  (Fin.fintype d))
                (@Couret.STROBO2TORS.recohSelectedTernaryFintype d q inst entries))) →
          ∀
            (bank :
              Fin k →
                @AddChar.{0, 0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addMonoid.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                        (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                  Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
            Not
              (@Set.InjOn.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) (Fin k → Complex)
                (fun T i =>
                  @Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (bank i) T)
                (@SetLike.coe.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                  (Finset.{0} ((i : Fin d) → ZMod (q i)))
                  (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                  (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (fun a b =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                        (Fin.fintype d) a b)
                    (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d)
                      fun a => @ZMod.fintype (q a) (inst a))
                    S))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_bank_minimal

