-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.singleton_collision_product_odd_annihilator_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:24:56.678171+00:00
-- url     : https://prove2.me/submissions/d8565dd6-d74d-45aa-897b-0d208eefbc60

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_c4_square_embedding_product_factor
import Theorems.Thm_Couret_InterIA_SingletonNecessity_four_torsion_trivial_of_odd_annihilator
import Theorems.Thm_Couret_InterIA_SingletonNecessity_singleton_collision_iff_contains_c4_square
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary Couret.InterIA.Parity
variable {P H : Type*} [AddCommGroup P] [AddCommGroup H]







theorem c4_square_embedding_product_iff
    (hH : ∀ y : H, (4:ℕ) • y=0 → y=0) :
    (∃ φ : G4 →+ P × H, Function.Injective φ) ↔
    (∃ ψ : G4 →+ P, Function.Injective ψ) := by
  constructor
  · rintro ⟨φ,hφ⟩
    exact c4_square_embedding_product_factor hH φ hφ
  · rintro ⟨ψ,hψ⟩
    let φ : G4 →+ P × H :=
      { toFun := fun z => (ψ z,0)
        map_zero' := by simp
        map_add' := fun a b => by simp }
    exact ⟨φ,fun a b hab => hψ (congrArg Prod.fst hab)⟩

theorem singleton_collision_product_iff [DecidableEq P] [DecidableEq H]
    (hH : ∀ y : H, (4:ℕ) • y=0 → y=0) :
    (∃ A B : Finset (P × H), A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) ↔
    (∃ A B : Finset P, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) := by
  rw [singleton_collision_iff_contains_c4_square,
    singleton_collision_iff_contains_c4_square]
  exact c4_square_embedding_product_iff hH

theorem p2m_local_singleton_collision_product_odd_annihilator_iff
    [DecidableEq P] [DecidableEq H] (k : ℕ)
    (hH : ∀ y : H, (2*k+1) • y=0) :
    (∃ A B : Finset (P × H), A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) ↔
    (∃ A B : Finset P, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) := by
  exact singleton_collision_product_iff (four_torsion_trivial_of_odd_annihilator k hH)

end Couret.InterIA.SingletonNecessity

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {P : Type p2m_u_0} {H : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} P] [inst_1 : AddCommGroup.{p2m_u_1} H]
  [inst_2 : DecidableEq.{p2m_u_0 + 1} P] [inst_3 : DecidableEq.{p2m_u_1 + 1} H] (k : Nat),
  (∀ (y : H),
      @Eq.{p2m_u_1 + 1} H
        (@HSMul.hSMul.{0, p2m_u_1, p2m_u_1} Nat H H
          (@instHSMul.{0, p2m_u_1} Nat H
            (@AddMonoid.toNSMul.{p2m_u_1} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          y)
        (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_1} H
            (@NegZeroClass.toZero.{p2m_u_1} H
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_1)))))))) →
    Iff
      (@Exists.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Finset.{max p2m_u_1 p2m_u_0} (Prod.{p2m_u_0, p2m_u_1} P H)) fun A =>
        @Exists.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Finset.{max p2m_u_1 p2m_u_0} (Prod.{p2m_u_0, p2m_u_1} P H)) fun B =>
          And
            (@Eq.{1} Nat (@Finset.card.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H) A)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (And
              (@Eq.{1} Nat (@Finset.card.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H) B)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (And
                (@Eq.{1} Nat
                  (@Finset.card.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
                    (@Inter.inter.{max p2m_u_0 p2m_u_1} (Finset.{max p2m_u_1 p2m_u_0} (Prod.{p2m_u_0, p2m_u_1} P H))
                      (@Finset.instInter.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H) fun a b =>
                        @instDecidableEqProd.{p2m_u_0, p2m_u_1} P H inst_2 inst_3 a b)
                      A B))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∀ (z : Prod.{p2m_u_0, p2m_u_1} P H),
                  @Eq.{1} Nat
                    (@Couret.InterIA.Parity.orderedSquare.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
                      (@Prod.instAddCommGroup.{p2m_u_0, p2m_u_1} P H inst inst_1)
                      (fun a b => @instDecidableEqProd.{p2m_u_0, p2m_u_1} P H inst_2 inst_3 a b) A z)
                    (@Couret.InterIA.Parity.orderedSquare.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
                      (@Prod.instAddCommGroup.{p2m_u_0, p2m_u_1} P H inst inst_1)
                      (fun a b => @instDecidableEqProd.{p2m_u_0, p2m_u_1} P H inst_2 inst_3 a b) B z)))))
      (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} P) fun A =>
        @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} P) fun B =>
          And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} P A) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (And
              (@Eq.{1} Nat (@Finset.card.{p2m_u_0} P B) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (And
                (@Eq.{1} Nat
                  (@Finset.card.{p2m_u_0} P
                    (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} P) (@Finset.instInter.{p2m_u_0} P inst_2) A B))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∀ (z : P),
                  @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} P inst inst_2 A z)
                    (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} P inst inst_2 B z))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_singleton_collision_product_odd_annihilator_iff

