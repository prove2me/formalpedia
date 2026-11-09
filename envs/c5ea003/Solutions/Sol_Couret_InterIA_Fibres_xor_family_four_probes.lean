-- Prove2me | solution 1 for Couret.InterIA.Fibres.xor_family_four_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:06:09.922575+00:00
-- url     : https://prove2.me/submissions/b31fd1fc-628d-48e6-8641-e9cc2e3bb0a3

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
import Theorems.Thm_Couret_InterIA_Fibres_xor_four_coordinate_separates
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





theorem xor_member_eq_first_of_two_differences {α : Type*} [DecidableEq α]
    (A B C : Finset α) (x : α) (hb : ¬ (x ∈ A ↔ x ∈ B)) (hc : ¬ (x ∈ A ↔ x ∈ C)) :
    x ∈ A ↔ x ∈ symmDiff (symmDiff A B) C := by
  simp only [Finset.mem_symmDiff]
  tauto



theorem p2m_local_xor_family_four_probes {α : Type*} [DecidableEq α]
    (P : Set (Finset α)) (hc : P.ncard=4) (hxor : XorClosed P) :
    ∃ q : Fin 2 → α, ProbeSeparates P q := by
  classical
  obtain ⟨A,B,C,E,hAB,hAC,_hAE,hBC,_hBE,_hCE,hP⟩ := Set.ncard_eq_four.mp hc
  let D := symmDiff (symmDiff A B) C
  have hDA : D ≠ A := by
    intro h
    apply hBC
    ext x
    have he : x ∈ D ↔ x ∈ A := by rw [h]
    dsimp only [D] at he
    simp only [Finset.mem_symmDiff] at he
    tauto
  have hDB : D ≠ B := by
    intro h
    apply hAC
    ext x
    have he : x ∈ D ↔ x ∈ B := by rw [h]
    dsimp only [D] at he
    simp only [Finset.mem_symmDiff] at he
    tauto
  have hDC : D ≠ C := by
    intro h
    apply hAB
    ext x
    have he : x ∈ D ↔ x ∈ C := by rw [h]
    dsimp only [D] at he
    simp only [Finset.mem_symmDiff] at he
    tauto
  have hD : D ∈ P := hxor A (by rw [hP]; simp) B (by rw [hP]; simp) C (by rw [hP]; simp)
  have hDE : D=E := by
    rw [hP] at hD
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hD
    tauto
  have hPD : P={A,B,C,D} := by rw [hDE,hP]
  obtain ⟨x,hx⟩ := exists_membership_difference A B hAB
  by_cases hsame : x ∈ A ↔ x ∈ C
  · obtain ⟨y,hy⟩ := exists_membership_difference A C hAC
    rw [hPD]
    exact ⟨_,xor_four_coordinate_separates A B C x y hx hsame hy⟩
  · have hsameD : x ∈ A ↔ x ∈ D := xor_member_eq_first_of_two_differences A B C x hx hsame
    obtain ⟨y,hy⟩ := exists_membership_difference A D hDA.symm
    have hback : symmDiff (symmDiff A B) D=C := symmDiff_symmDiff_cancel_left _ _
    have hswap : P={A,B,D,symmDiff (symmDiff A B) D} := by
      rw [hback,hPD]
      ext T
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      exact or_congr Iff.rfl (or_congr Iff.rfl or_comm)
    rw [hswap]
    exact ⟨_,xor_four_coordinate_separates A B D x y hx hsameD hy⟩















end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (P : Set.{p2m_u_0} (Finset.{p2m_u_0} α)),
  @Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Couret.InterIA.Fibres.XorClosed.{p2m_u_0} α inst P →
      @Exists.{p2m_u_0 + 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → α) fun q =>
        @Couret.InterIA.Fibres.ProbeSeparates.{p2m_u_0} α inst
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) P q := @_root_.Couret.InterIA.Fibres.p2m_local_xor_family_four_probes

