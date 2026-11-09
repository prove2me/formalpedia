-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.nonzero_of_distinctLabels
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:15.003463+00:00
-- url     : https://prove2.me/submissions/1f70a289-5d99-4843-aa46-e1eda58a1bab

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]










theorem evaluation_label (x : Fin 6 → G) (i : Fin 7) :
    evaluation x (label i.val) = Fin.cases 0 x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [label]
  · change evaluation x (label (j.val+1))=x j
    rw [label,if_neg (by omega),Nat.add_sub_cancel]
    exact evaluation_basis x j



theorem p2m_local_nonzero_of_distinctLabels (x : Fin 6 → G) (hd : SevenDistinct x) :
    ∀ i, x i ≠ 0 := by
  intro i h
  have he : evaluation x (label i.succ.val)=evaluation x (label (0:Fin 7).val) := by
    rw [evaluation_label,evaluation_label]
    exact h
  have hi := hd he
  exact Fin.succ_ne_zero i hi





end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))),
      @Ne.{p2m_u_0 + 1} G (x i)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_nonzero_of_distinctLabels

