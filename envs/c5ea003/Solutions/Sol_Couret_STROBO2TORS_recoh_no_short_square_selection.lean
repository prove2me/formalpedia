-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_no_short_square_selection
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:30.382165+00:00
-- url     : https://prove2.me/submissions/af9f384d-3ca6-4c56-a693-8898076ad1fd

import Aesop
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_double_fibre_rank_succ_le_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_exceptional_fibre_of_positive_ranks
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_card_le_two_pow_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_selection_injective_on_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_card_eq_nat_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
Optimal character banks selected from the observed labelled ordered square.
The selected bank is fixed on its entire fibre. Selection is existential;
this module does not implement selection from raw or typed decoder input.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























/-- A shorter square-selection rule fails on a genuine triple whenever the
domain is nonempty. In positive binary and ternary rank, one exceptional
fibre alone forces the additional character slot. -/
theorem p2m_local_recoh_no_short_square_selection (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) (k : ℕ)
    (hk : k < recohAfterSquareBudget r s)
    (select : (G → ℕ) → (Fin k → AddChar G ℂ)) :
    ¬ Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohSquareSelectedObservation select S.1) := by
  intro hinj
  by_cases hr : r = 0
  · simp [recohAfterSquareBudget, hr] at hk
  · have hrpos : 0 < r := by omega
    by_cases hs : s = 0
    · have hkr : k < r := by simpa [recohAfterSquareBudget, hr, hs] using hk
      obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset G)) (n := 3) (by simpa using hG3)
      have hsep := recoh_square_selection_injective_on_fibre select hinj S
      have hupper := recoh_fibre_card_le_two_pow_of_separating_bank S
        (select (orderedSquare S)) hsep
      have hlower : 2 ^ r ≤ (squareFibre S).card := by
        calc
          2 ^ r = (torsionOrbit S).card := by
            rw [torsionOrbit_card S hS, recoh_two_torsion_card_eq_nat_card, hcard2]
          _ ≤ (squareFibre S).card := Finset.card_le_card (torsionOrbit_subset_fibre S hS)
      have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) hkr
      omega
    · have hspos : 0 < s := by omega
      have hs1 : 1 ≤ s := hspos
      have hkr : k < r + 1 := by
        simpa only [recohAfterSquareBudget, if_neg hr, Nat.min_eq_left hs1] using hk
      obtain ⟨S, _, hF⟩ :=
        recoh_exists_exceptional_fibre_of_positive_ranks r s hrpos hspos hcard2 hcard3
      have hFpow : (squareFibre S).card = 2 * 2 ^ r := by
        rw [hF, recoh_two_torsion_card_eq_nat_card, hcard2]
      have hsep := recoh_square_selection_injective_on_fibre select hinj S
      have hmin := recoh_double_fibre_rank_succ_le_of_separating_bank S r hFpow
        (select (orderedSquare S)) hsep
      omega







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r s : Nat),
  @Eq.{1} Nat
      (Nat.card.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    @Eq.{1} Nat
        (Nat.card.{p2m_u_0}
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              x))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Fintype.card.{p2m_u_0} G inst_2) →
        ∀ (k : Nat),
          @LT.lt.{0} Nat instLTNat k (Couret.STROBO2TORS.recohAfterSquareBudget r s) →
            ∀
              (select :
                (G → Nat) →
                  Fin k →
                    @AddChar.{p2m_u_0, 0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
              Not
                (@Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
                  (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
                    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (Prod.{p2m_u_0, 0} (G → Nat) (Fin k → Complex)) fun S =>
                  @Couret.STROBO2TORS.recohSquareSelectedObservation.{p2m_u_0} G inst inst_1 k select
                    (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                      (fun S =>
                        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_no_short_square_selection

