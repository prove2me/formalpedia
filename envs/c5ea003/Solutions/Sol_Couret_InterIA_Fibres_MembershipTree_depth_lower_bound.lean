-- Prove2me | solution 1 for Couret.InterIA.Fibres.MembershipTree.depth_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:41:18.051789+00:00
-- url     : https://prove2.me/submissions/750eee87-9f18-4e02-a9a1-97b22d2a40e7

import Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5
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
import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset



namespace MembershipTree









theorem run_mem_leaves {α : Type*} [DecidableEq α] (tree : MembershipTree α) (T : Finset α) :
    tree.run T ∈ tree.leaves := by
  induction tree with
  | leaf U => simp [run,leaves]
  | query x no yes hn hy =>
    by_cases hx : x ∈ T
    · simp only [run,if_pos hx,leaves]
      exact Finset.mem_union.mpr (Or.inr hy)
    · simp only [run,if_neg hx,leaves]
      exact Finset.mem_union.mpr (Or.inl hn)

theorem leaves_card_le_pow_depth {α : Type*} [DecidableEq α] (tree : MembershipTree α) :
    tree.leaves.card ≤ 2^tree.depth := by
  induction tree with
  | leaf U => simp [leaves,depth]
  | query x no yes hn hy =>
    have hn' := Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_max_left no.depth yes.depth)
    have hy' := Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_max_right no.depth yes.depth)
    change (no.leaves ∪ yes.leaves).card ≤ 2^(max no.depth yes.depth+1)
    calc _ ≤ no.leaves.card+yes.leaves.card := Finset.card_union_le _ _
         _ ≤ 2^(max no.depth yes.depth)+2^(max no.depth yes.depth) := Nat.add_le_add (hn.trans hn') (hy.trans hy')
         _ = _ := by rw [pow_succ]; omega

/-- The lower bound applies to every adaptive tree, including queries that add no information. -/
theorem candidate_card_le_pow_depth {α : Type*} [DecidableEq α]
    (tree : MembershipTree α) (P : Set (Finset α)) (hc : tree.CorrectOn P) :
    P.ncard ≤ 2^tree.depth := by
  have hsub : P ⊆ (tree.leaves : Set (Finset α)) := by
    intro T hT
    have hm := tree.run_mem_leaves T
    rw [hc T hT] at hm
    exact hm
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  exact hcard.trans tree.leaves_card_le_pow_depth

theorem p2m_local_depth_lower_bound {α : Type*} [DecidableEq α]
    (tree : MembershipTree α) (P : Set (Finset α)) (d : ℕ)
    (hcard : P.ncard=2^d) (hc : tree.CorrectOn P) : d ≤ tree.depth := by
  have hb := tree.candidate_card_le_pow_depth P hc
  rw [hcard] at hb
  by_contra hn
  have ht : 2^tree.depth < 2^d := Nat.pow_lt_pow_right (by omega) (by omega)
  omega







end MembershipTree
end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (tree : Couret.InterIA.Fibres.MembershipTree.{p2m_u_0} α)
  (P : Set.{p2m_u_0} (Finset.{p2m_u_0} α)) (d : Nat),
  @Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d) →
    @Couret.InterIA.Fibres.MembershipTree.CorrectOn.{p2m_u_0} α inst tree P →
      @LE.le.{0} Nat instLENat d (@Couret.InterIA.Fibres.MembershipTree.depth.{p2m_u_0} α tree) := @_root_.Couret.InterIA.Fibres.MembershipTree.p2m_local_depth_lower_bound

