-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_optimal_fibre_bank_size
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:32.875696+00:00
-- url     : https://prove2.me/submissions/8d92fdcd-3eb6-4b97-b7f3-4dd43508877e

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_exceptional_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_ordinary_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_exceptional
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_ordinary
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_rank_le_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_card_eq_nat_card
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









/-- Exact optimality on each full triple fibre. The lower bound covers every
bank of complex characters, including repeated or vanishing probes. -/
theorem p2m_local_recoh_optimal_fibre_bank_size (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (S : Finset G) (hS : S.card = 3) :
    (∃ bank : Fin (recohFibreBudget S) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) ∧
    (∀ k : ℕ, k < recohFibreBudget S → ∀ bank : Fin k → AddChar G ℂ,
      ¬ Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) := by
  rcases squareFibre_card_h_or_two_h S hS with ho | he
  · rw [recoh_fibre_budget_ordinary r hcard2 S ho]
    refine ⟨recoh_exists_bank_on_ordinary_fibre r hcard2 S hS ho, ?_⟩
    intro k hk bank hsep
    have hpow : (squareFibre S).card = 2 ^ r := by
      rw [ho, recoh_two_torsion_card_eq_nat_card, hcard2]
    exact (Nat.not_lt_of_ge (recoh_fibre_rank_le_of_separating_bank
      S r hpow bank hsep)) hk
  · rw [recoh_fibre_budget_exceptional r hcard2 S he]
    refine ⟨recoh_exists_bank_on_exceptional_fibre r hcard2 S hS he, ?_⟩
    intro k hk bank hsep
    have hpow : (squareFibre S).card = 2 * 2 ^ r := by
      rw [he, recoh_two_torsion_card_eq_nat_card, hcard2]
    exact (Nat.not_lt_of_ge (recoh_double_fibre_rank_succ_le_of_separating_bank
      S r hpow bank hsep)) hk

























end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r : Nat),
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
    ∀ (S : Finset.{p2m_u_0} G),
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        And
          (@Exists.{p2m_u_0 + 1}
            (Fin (@Couret.STROBO2TORS.recohFibreBudget.{p2m_u_0} G inst inst_1 inst_2 S) →
              @AddChar.{p2m_u_0, 0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
            fun bank =>
            @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G)
              (Fin (@Couret.STROBO2TORS.recohFibreBudget.{p2m_u_0} G inst inst_1 inst_2 S) → Complex)
              (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
              (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)))
          (∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat k (@Couret.STROBO2TORS.recohFibreBudget.{p2m_u_0} G inst inst_1 inst_2 S) →
              ∀
                (bank :
                  Fin k →
                    @AddChar.{p2m_u_0, 0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
                Not
                  (@Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G) (Fin k → Complex)
                    (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
                    (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                      (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
                      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_optimal_fibre_bank_size

