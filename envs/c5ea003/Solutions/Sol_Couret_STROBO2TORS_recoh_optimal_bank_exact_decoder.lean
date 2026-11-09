-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_optimal_bank_exact_decoder
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:56:26.082631+00:00
-- url     : https://prove2.me/submissions/d8218685-89e7-4c25-9212-c5ec806af162

import Aesop
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exact_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_bank_size
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
Structured candidates for exact RECOH reconstruction.

For a genuine triple S = {a,b,c}, its three distinct off-diagonal sums
E = {a+b,a+c,b+c} belong to the support of the ordered square.  With
sigma = a+b+c, they satisfy sum E = sigma+sigma and S = sigma-E.
This supplies a complete candidate generator using only the input square.

The finite candidate generator uses decidable group operations.  The exact
complex-character filter below is explicitly noncomputable: this module
certifies its mathematical result, not an executable representation of
complex numbers or a refinement of a separate Python implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







variable [Fintype G]























/-- The previously certified optimum admits the exact candidate decoder,
for every triple, with no additional character-separation hypothesis. -/
theorem p2m_local_recoh_optimal_bank_exact_decoder
    (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) :
    ∃ bank : Fin (recohOptimalBudget r s) → AddChar G ℂ,
      ∀ S : Finset G, S.card = 3 →
        recohExactDecoder bank (recohObservation bank S) = {S} := by
  obtain ⟨⟨bank, hinj⟩, _⟩ := recoh_optimal_bank_size r s hcard2 hcard3 hG3
  exact ⟨bank, fun S hS => recoh_exact_decoder_singleton bank hinj S hS⟩

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
        @Exists.{p2m_u_0 + 1}
          (Fin (Couret.STROBO2TORS.recohOptimalBudget r s) →
            @AddChar.{p2m_u_0, 0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          fun bank =>
          ∀ (S : Finset.{p2m_u_0} G),
            @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, 0} G inst inst_1 inst_2
                  (Fin (Couret.STROBO2TORS.recohOptimalBudget r s)) bank
                  (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, 0} G inst inst_1
                    (Fin (Couret.STROBO2TORS.recohOptimalBudget r s)) bank S))
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                  (@Finset.instSingleton.{p2m_u_0} (Finset.{p2m_u_0} G)) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_optimal_bank_exact_decoder

