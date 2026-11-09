-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_reconstructing_empty_bank
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:10.609822+00:00
-- url     : https://prove2.me/submissions/a0ec1f2b-bbc9-4feb-8f4a-8167ffd75f37

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_injective_of_trivial_two_torsion
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
The optimal size of a fixed bank of individual, labelled complex
Fourier coefficients, given the labelled ordered convolution square of a
three-element support.  Zero is allowed in the support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]



/-- Rank zero in two-torsion needs no additional character coefficient. -/
theorem p2m_local_recoh_exists_reconstructing_empty_bank
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ 0) :
    ∃ bank : Fin 0 → AddChar G ℂ,
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohObservation bank S.1) := by
  obtain ⟨bank2, _, hsep2⟩ := recoh_two_primary_characters_of_card 0 hcard2
  refine ⟨Fin.elim0, ?_⟩
  intro S T h
  apply recoh_square_injective_of_trivial_two_torsion
    (fun u hu => hsep2 u hu (fun i => Fin.elim0 i))
  exact congrArg Prod.fst h





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G],
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
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Exists.{p2m_u_0 + 1}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @AddChar.{p2m_u_0, 0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      fun bank =>
      @Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
        (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Prod.{p2m_u_0, 0} (G → Nat) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Complex))
        fun S =>
        @Couret.STROBO2TORS.recohObservation.{p2m_u_0, 0} G inst inst_1
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) bank
          (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (fun S =>
              @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_reconstructing_empty_bank

