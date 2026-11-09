-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_after_square_fibre_bank
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:27.670623+00:00
-- url     : https://prove2.me/submissions/e4d4cd8a-0efd-45bf-9ac7-7272d7202b6f

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_exceptional_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_ordinary_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_bank_rank_sum
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_empty_bank
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
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











/-- A globally reconstructing fixed bank separates every complete fibre. -/
theorem recoh_fixed_bank_injective_on_fibre {k : ℕ}
    (bank : Fin k → AddChar G ℂ)
    (hinj : Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation bank S.1)) (S : Finset G) :
    Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (squareFibre S) := by
  intro T hT U hU heq
  obtain ⟨hT3, hsT⟩ := (mem_squareFibre S T).mp hT
  obtain ⟨hU3, hsU⟩ := (mem_squareFibre S U).mp hU
  have hobs : recohObservation bank T = recohObservation bank U := by
    apply Prod.ext
    · funext z
      exact (hsT z).symm.trans (hsU z)
    · exact heq
  exact congrArg Subtype.val (hinj (a₁ := ⟨T, hT3⟩) (a₂ := ⟨U, hU3⟩) hobs)

/-- A bank can be padded with trivial characters without losing separation. -/
theorem recoh_fibre_bank_mono (S : Finset G) {k l : ℕ} (hkl : k ≤ l)
    (bank : Fin k → AddChar G ℂ)
    (hsep : Set.InjOn
      (fun T : Finset G => fun i => recohSupportProbe (bank i) T) (squareFibre S)) :
    ∃ larger : Fin l → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (larger i) T)
        (squareFibre S) := by
  classical
  let larger : Fin l → AddChar G ℂ :=
    fun i => if hi : i.val < k then bank ⟨i.val, hi⟩ else 1
  refine ⟨larger, ?_⟩
  intro T hT U hU heq
  apply hsep hT hU
  funext i
  have h := congrFun heq (Fin.castLE hkl i)
  simpa [larger, i.isLt] using h



/-- Every fibre admits a bank bounded by the stated worst-case budget. -/
theorem p2m_local_recoh_exists_after_square_fibre_bank (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (S : Finset G) (hS : S.card = 3) :
    ∃ bank : Fin (recohAfterSquareBudget r s) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S) := by
  by_cases hr : r = 0
  · subst r
    rw [show recohAfterSquareBudget 0 s = 0 by simp [recohAfterSquareBudget]]
    obtain ⟨bank, hinj⟩ := recoh_exists_reconstructing_empty_bank hcard2
    exact ⟨bank, recoh_fixed_bank_injective_on_fibre bank hinj S⟩
  · by_cases hs : s = 0
    · subst s
      rw [show recohAfterSquareBudget r 0 = r by simp [recohAfterSquareBudget, hr]]
      obtain ⟨bank, hinj⟩ := recoh_exists_reconstructing_bank_rank_sum r 0 hcard2 hcard3
      exact ⟨bank, recoh_fixed_bank_injective_on_fibre bank hinj S⟩
    · have hs1 : 1 ≤ s := by omega
      rw [show recohAfterSquareBudget r s = r + 1 by
        simp [recohAfterSquareBudget, hr, Nat.min_eq_left hs1]]
      rcases squareFibre_card_h_or_two_h S hS with ho | he
      · obtain ⟨bank, hsep⟩ := recoh_exists_bank_on_ordinary_fibre r hcard2 S hS ho
        exact recoh_fibre_bank_mono S (by omega : r ≤ r + 1) bank hsep
      · exact recoh_exists_bank_on_exceptional_fibre r hcard2 S hS he

















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
      ∀ (S : Finset.{p2m_u_0} G),
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          @Exists.{p2m_u_0 + 1}
            (Fin (Couret.STROBO2TORS.recohAfterSquareBudget r s) →
              @AddChar.{p2m_u_0, 0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
            fun bank =>
            @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G) (Fin (Couret.STROBO2TORS.recohAfterSquareBudget r s) → Complex)
              (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
              (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_after_square_fibre_bank

