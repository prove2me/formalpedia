-- Prove2me | solution 1 for Couret.InterIA.Fibres.xor_family_fixed_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:52.718824+00:00
-- url     : https://prove2.me/submissions/bb1c5416-57ad-4170-9b82-ecae5727ca54

import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_xor_family_four_probes
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity



theorem exists_membership_difference {α : Type*} [DecidableEq α]
    (A B : Finset α) (hne : A ≠ B) : ∃ x, ¬ (x ∈ A ↔ x ∈ B) := by
  classical
  by_contra hn
  apply hne
  ext x
  by_contra hx
  exact hn ⟨x,hx⟩











/-- The quantifier order fixes the probes before any unknown candidate or answer. -/
theorem p2m_local_xor_family_fixed_probes {α : Type*} [DecidableEq α]
    (P : Set (Finset α)) (hc : P.ncard=1 ∨ P.ncard=2 ∨ P.ncard=4) (hxor : XorClosed P) :
    ∃ d : ℕ, d ≤ 2 ∧ P.ncard=2^d ∧ ∃ q : Fin d → α, ProbeSeparates P q := by
  classical
  rcases hc with h|h|h
  · obtain ⟨A,hP⟩ := Set.ncard_eq_one.mp h
    refine ⟨0,by omega,by simpa using h,Fin.elim0,?_⟩
    intro T hT U hU _
    rw [hP] at hT hU
    exact (Set.mem_singleton_iff.mp hT).trans (Set.mem_singleton_iff.mp hU).symm
  · obtain ⟨A,B,hAB,hP⟩ := Set.ncard_eq_two.mp h
    obtain ⟨x,hx⟩ := exists_membership_difference A B hAB
    refine ⟨1,by omega,by simpa using h,(fun _ => x),?_⟩
    intro T hT U hU he
    have he0 := he 0
    change x ∈ T ↔ x ∈ U at he0
    rw [hP] at hT hU
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hT hU
    rcases hT with rfl|rfl <;> rcases hU with rfl|rfl
    all_goals first | rfl | (exfalso; tauto)
  · obtain ⟨q,hq⟩ := xor_family_four_probes P h hxor
    exact ⟨2,by omega,by simpa using h,q,hq⟩













end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (P : Set.{p2m_u_0} (Finset.{p2m_u_0} α)),
  Or
      (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (Or
        (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) →
    @Couret.InterIA.Fibres.XorClosed.{p2m_u_0} α inst P →
      @Exists.{1} Nat fun d =>
        And (@LE.le.{0} Nat instLENat d (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (And
            (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
            (@Exists.{p2m_u_0 + 1} (Fin d → α) fun q => @Couret.InterIA.Fibres.ProbeSeparates.{p2m_u_0} α inst d P q)) := @_root_.Couret.InterIA.Fibres.p2m_local_xor_family_fixed_probes

