-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.parity_relabel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:29.572376+00:00
-- url     : https://prove2.me/submissions/21cf4179-5e61-4d81-b1ac-46c0e3aadeba

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_has_pairing
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_reindex
import Theorems.Thm_Couret_InterIA_SingletonNecessity_supportLeft_reindex
import Theorems.Thm_Couret_InterIA_SingletonNecessity_supportRight_reindex
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem p2m_local_parity_relabel (x : Fin 6 → G) (hd : SevenDistinct x)
    (hp : FibreParity (fun i => x i+x i)) :
    ∃ y : Fin 6 → G, SevenDistinct y ∧ supportLeft y=supportLeft x ∧
      supportRight y=supportRight x ∧ (CrossDoubles y ∨ MixedDoubles y) := by
  have h := parity_has_pairing (fun i => x i+x i) hp
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,4,5,3] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 1+x 1 ∧ x 4+x 4=x 5+x 5 ∧ x 2+x 2=x 3+x 3)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,3,5,4] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 1+x 1 ∧ x 3+x 3=x 5+x 5 ∧ x 2+x 2=x 4+x 4)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,3,4,5] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 1+x 1 ∧ x 3+x 3=x 4+x 4 ∧ x 2+x 2=x 5+x 5)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,2,1,4,5,3] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 2+x 2 ∧ x 4+x 4=x 5+x 5 ∧ x 1+x 1=x 3+x 3)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,2,1,3,5,4] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 2+x 2 ∧ x 3+x 3=x 5+x 5 ∧ x 1+x 1=x 4+x 4)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,2,1,3,4,5] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 0+x 0=x 2+x 2 ∧ x 3+x 3=x 4+x 4 ∧ x 1+x 1=x 5+x 5)
    exact ⟨h.1,h.2.2,h.2.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([1,2,0,4,5,3] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 1+x 1=x 2+x 2 ∧ x 4+x 4=x 5+x 5 ∧ x 0+x 0=x 3+x 3)
    exact ⟨h.2.1,h.2.2,h.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,3,4,5] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 3+x 3 ∧ x 1+x 1=x 4+x 4 ∧ x 2+x 2=x 5+x 5)
    exact ⟨h.1,h.2.1,h.2.2⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,3,5,4] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 3+x 3 ∧ x 1+x 1=x 5+x 5 ∧ x 2+x 2=x 4+x 4)
    exact ⟨h.1,h.2.1,h.2.2⟩
  · let p : Fin 6 → Fin 6 := fun i => ([1,2,0,3,5,4] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 1+x 1=x 2+x 2 ∧ x 3+x 3=x 5+x 5 ∧ x 0+x 0=x 4+x 4)
    exact ⟨h.2.1,h.2.2,h.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,4,3,5] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 4+x 4 ∧ x 1+x 1=x 3+x 3 ∧ x 2+x 2=x 5+x 5)
    exact ⟨h.1,h.2.1,h.2.2⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,4,5,3] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 4+x 4 ∧ x 1+x 1=x 5+x 5 ∧ x 2+x 2=x 3+x 3)
    exact ⟨h.1,h.2.1,h.2.2⟩
  · let p : Fin 6 → Fin 6 := fun i => ([1,2,0,3,4,5] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inr ?_⟩
    change (x 1+x 1=x 2+x 2 ∧ x 3+x 3=x 4+x 4 ∧ x 0+x 0=x 5+x 5)
    exact ⟨h.2.1,h.2.2,h.1⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,5,3,4] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 5+x 5 ∧ x 1+x 1=x 3+x 3 ∧ x 2+x 2=x 4+x 4)
    exact ⟨h.1,h.2.1,h.2.2⟩
  · let p : Fin 6 → Fin 6 := fun i => ([0,1,2,5,4,3] : List (Fin 6))[i.val]!
    have hi : Function.Injective p := by decide
    have hl : ({0,1,2}:Finset (Fin 6)).image p={0,1,2} := by decide
    have hr : ({3,4,5}:Finset (Fin 6)).image p={3,4,5} := by decide
    refine ⟨reindex x p,sevenDistinct_reindex x hd p hi,
      supportLeft_reindex x p hl,supportRight_reindex x p hr,Or.inl ?_⟩
    change (x 0+x 0=x 5+x 5 ∧ x 1+x 1=x 4+x 4 ∧ x 2+x 2=x 3+x 3)
    exact ⟨h.1,h.2.1,h.2.2⟩

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    (@Couret.InterIA.SingletonNecessity.FibreParity.{p2m_u_0} G inst_1 fun i =>
        @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          (x i) (x i)) →
      @Exists.{p2m_u_0 + 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G) fun y =>
        And (@Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst y)
          (And
            (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
              (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 y)
              (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 x))
            (And
              (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 y)
                (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x))
              (Or (@Couret.InterIA.SingletonNecessity.CrossDoubles.{p2m_u_0} G inst y)
                (@Couret.InterIA.SingletonNecessity.MixedDoubles.{p2m_u_0} G inst y)))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_parity_relabel

