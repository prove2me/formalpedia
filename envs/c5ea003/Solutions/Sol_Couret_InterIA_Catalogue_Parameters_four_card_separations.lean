-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Parameters.four_card_separations
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:55.203062+00:00
-- url     : https://prove2.me/submissions/135ba156-3a97-48f7-99ae-37bda834c587

import Definitions.Def_Couret_AffineParameterControls_321393084939
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]

theorem p2m_local_four_card_separations (a b c d : G) (hc : ({a,b,c,d} : Finset G).card=4) :
    c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    subst c
    have hs : ({a,b,a,d} : Finset G)={a,b,d} := by ext z; simp only [mem_insert,mem_singleton]; tauto
    rw [hs] at hc
    have hl : ({a,b,d} : Finset G).card ≤ 3 := Finset.card_le_three
    omega
  · intro he
    subst c
    have hs : ({a,b,b,d} : Finset G)={a,b,d} := by ext z; simp only [mem_insert,mem_singleton]; tauto
    rw [hs] at hc
    have hl : ({a,b,d} : Finset G).card ≤ 3 := Finset.card_le_three
    omega
  · intro he
    subst d
    have hs : ({a,b,c,a} : Finset G)={a,b,c} := by ext z; simp only [mem_insert,mem_singleton]; tauto
    rw [hs] at hc
    have hl : ({a,b,c} : Finset G).card ≤ 3 := Finset.card_le_three
    omega
  · intro he
    subst d
    have hs : ({a,b,c,b} : Finset G)={a,b,c} := by ext z; simp only [mem_insert,mem_singleton]; tauto
    rw [hs] at hc
    have hl : ({a,b,c} : Finset G).card ≤ 3 := Finset.card_le_three
    omega











end Couret.InterIA.Catalogue.Parameters

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} G] (a b c d : G),
  @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} G
        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst) a
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst) b
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst) c
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) d)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    And (@Ne.{p2m_u_0 + 1} G c a)
      (And (@Ne.{p2m_u_0 + 1} G c b) (And (@Ne.{p2m_u_0 + 1} G d a) (@Ne.{p2m_u_0 + 1} G d b))) := @_root_.Couret.InterIA.Catalogue.Parameters.p2m_local_four_card_separations

