-- Prove2me | solution 1 for Couret.InterIA.Fibres.xor_four_coordinate_separates
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:55.672947+00:00
-- url     : https://prove2.me/submissions/db5c355c-872c-45cd-8f38-009755d7f1a6

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
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity





theorem xor_member_eq_middle {α : Type*} [DecidableEq α] (A B C : Finset α) (x : α)
    (hc : x ∈ A ↔ x ∈ C) : x ∈ symmDiff (symmDiff A B) C ↔ x ∈ B := by
  simp only [Finset.mem_symmDiff]
  tauto

theorem xor_member_ne_middle {α : Type*} [DecidableEq α] (A B C : Finset α) (x : α)
    (hc : ¬ (x ∈ A ↔ x ∈ C)) : ¬ (x ∈ B ↔ x ∈ symmDiff (symmDiff A B) C) := by
  simp only [Finset.mem_symmDiff]
  tauto



theorem p2m_local_xor_four_coordinate_separates {α : Type*} [DecidableEq α]
    (A B C : Finset α) (x y : α)
    (hx : ¬ (x ∈ A ↔ x ∈ B)) (hc : x ∈ A ↔ x ∈ C)
    (hy : ¬ (y ∈ A ↔ y ∈ C)) :
    ProbeSeparates ({A,B,C,symmDiff (symmDiff A B) C} : Set (Finset α))
      (fun i : Fin 2 => if i=0 then x else y) := by
  let D := symmDiff (symmDiff A B) C
  have hDx : x ∈ D ↔ x ∈ B := xor_member_eq_middle A B C x hc
  have hDy : ¬ (y ∈ B ↔ y ∈ D) := xor_member_ne_middle A B C y hy
  have hAD : ¬ (x ∈ A ↔ x ∈ D) := fun h => hx (h.trans hDx)
  have hBC : ¬ (x ∈ B ↔ x ∈ C) := fun h => hx (hc.trans h.symm)
  have hCD : ¬ (x ∈ C ↔ x ∈ D) := fun h => hx (hc.trans (h.trans hDx))
  intro T hT U hU he
  have he0 := he 0
  have he1 := he 1
  change x ∈ T ↔ x ∈ U at he0
  change y ∈ T ↔ y ∈ U at he1
  clear he
  change T ∈ ({A,B,C,D} : Set (Finset α)) at hT
  change U ∈ ({A,B,C,D} : Set (Finset α)) at hU
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hT hU
  rcases hT with rfl|rfl|rfl|rfl <;> rcases hU with rfl|rfl|rfl|rfl
  all_goals first
    | rfl
    | exact False.elim (hx he0)
    | exact False.elim (hx he0.symm)
    | exact False.elim (hAD he0)
    | exact False.elim (hAD he0.symm)
    | exact False.elim (hBC he0)
    | exact False.elim (hBC he0.symm)
    | exact False.elim (hCD he0)
    | exact False.elim (hCD he0.symm)
    | exact False.elim (hy he1)
    | exact False.elim (hy he1.symm)
    | exact False.elim (hDy he1)
    | exact False.elim (hDy he1.symm)

















end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (A B C : Finset.{p2m_u_0} α) (x y : α),
  Not
      (Iff
        (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) A x)
        (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) B x)) →
    Iff
        (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) A x)
        (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) C x) →
      Not
          (Iff
            (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) A y)
            (@Membership.mem.{p2m_u_0, p2m_u_0} α (Finset.{p2m_u_0} α)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) α (@Finset.instSetLike.{p2m_u_0} α)) C
              y)) →
        @Couret.InterIA.Fibres.ProbeSeparates.{p2m_u_0} α inst
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Insert.insert.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
            (@Set.instInsert.{p2m_u_0} (Finset.{p2m_u_0} α)) A
            (@Insert.insert.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
              (@Set.instInsert.{p2m_u_0} (Finset.{p2m_u_0} α)) B
              (@Insert.insert.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
                (@Set.instInsert.{p2m_u_0} (Finset.{p2m_u_0} α)) C
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
                  (@Set.instSingletonSet.{p2m_u_0} (Finset.{p2m_u_0} α))
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instLattice.{p2m_u_0} α inst)))
                    (@Finset.instSDiff.{p2m_u_0} α inst)
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α)
                          (@Finset.instLattice.{p2m_u_0} α inst)))
                      (@Finset.instSDiff.{p2m_u_0} α inst) A B)
                    C)))))
          fun i =>
          @ite.{p2m_u_0 + 1} α
            (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) i
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
            x y := @_root_.Couret.InterIA.Fibres.p2m_local_xor_four_coordinate_separates

