-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.distinct_values
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:04.692487+00:00
-- url     : https://prove2.me/submissions/019d63e0-af0f-4e04-9f89-c415ad138d20

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_MatchingElimination_8675038abe55
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem p2m_local_distinct_values (x : Fin 6 → G) (hd : DistinctLabels x) :
    Function.Injective x := by
  intro i j hij
  have hi : i.val+1<7 := by omega
  have hj : j.val+1<7 := by omega
  have hei : evaluation x (label (i.val+1))=x i := by
    rw [label,if_neg (by omega),Nat.add_sub_cancel]
    exact evaluation_basis x i
  have hej : evaluation x (label (j.val+1))=x j := by
    rw [label,if_neg (by omega),Nat.add_sub_cancel]
    exact evaluation_basis x j
  have he : (⟨i.val+1,hi⟩ : Fin 7) = ⟨j.val+1,hj⟩ := by
    apply hd
    change evaluation x (label (i.val+1))=evaluation x (label (j.val+1))
    rw [hei,hej,hij]
  apply Fin.ext
  have hv : i.val+1=j.val+1 := congrArg Fin.val he
  exact Nat.add_right_cancel hv





end Couret.InterIA.SingletonNecessity


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.DistinctLabels.{p2m_u_0} G inst x →
    @Function.Injective.{1, p2m_u_0 + 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) G x := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_distinct_values

