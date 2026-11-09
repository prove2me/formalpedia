-- Prove2me | solution 1 for Couret.STROBO2TORS.pairLifts_card_balance
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:54.233936+00:00
-- url     : https://prove2.me/submissions/e17225ad-d094-4584-b335-d90f5ff7a154

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_both_zero_iff
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts_card
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Theorems.Thm_Couret_STROBO2TORS_translated_zero_lifts_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]











/-- The six-forbidden-values balance, with the unique singleton overlap.
It is valid before any natural-number subtraction. -/
theorem p2m_local_pairLifts_card_balance (d v : G)
    (hd : d+d=0) (hd0 : d ≠ 0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) :
    (pairLifts d v).card + 6 * (twoTorsion : Finset G).card =
      Fintype.card G * (twoTorsion : Finset G).card + 1 := by
  let U := (Finset.univ : Finset G) ×ˢ (twoTorsion : Finset G)
  let A := U.filter (fun p => 0 ∈ paramSupport ((p.1,d),v))
  let B := U.filter (fun p => 0 ∈ translateSupport (paramSupport ((p.1,d),-v)) p.2)
  have hA : A.card = 3 * (twoTorsion : Finset G).card := by
    have he : A = ((Finset.univ : Finset G).filter
        (fun a => 0 ∈ paramSupport ((a,d),v))) ×ˢ (twoTorsion : Finset G) := by
      ext p; simp [A,U,and_comm]
    rw [he, Finset.card_product, paramSupport_zero_lifts_card d v hd hd0 hv hv0]
  have hB : B.card = 3 * (twoTorsion : Finset G).card := by
    calc
      B.card = ∑ u ∈ (twoTorsion : Finset G),
          ((Finset.univ : Finset G).filter
            (fun a => 0 ∈ translateSupport (paramSupport ((a,d),-v)) u)).card := by
        simp only [B,U,Finset.card_eq_sum_ones,Finset.sum_filter]
        exact Finset.sum_product_right _ _ _
      _ = ∑ _u ∈ (twoTorsion : Finset G), 3 := by
        apply Finset.sum_congr rfl
        intro u _
        exact translated_zero_lifts_card d (-v) u hd hd0
          (three_torsion_neg v hv) (neg_ne_zero.mpr hv0)
      _ = _ := by simp [Nat.mul_comm]
  have hAB : A ∩ B = {(0,0)} := by
    ext p
    rcases p with ⟨a,u⟩
    simp only [A,B,U,Finset.mem_inter,Finset.mem_filter,Finset.mem_product,
      Finset.mem_univ,true_and,Finset.mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hu,ha⟩,⟨_,hb⟩⟩
      exact (paramSupport_both_zero_iff a d v u hd hv hv0 ((mem_twoTorsion u).mp hu)).mp ⟨ha,hb⟩
    · rintro ⟨rfl,rfl⟩
      have hz : (0:G) ∈ twoTorsion := (mem_twoTorsion _).mpr (by simp)
      simp [hz,paramSupport,translateSupport]
  have hcomp : pairLifts d v = U \ (A ∪ B) := by
    ext p; simp [pairLifts,U,A,B]; tauto
  have hsub : A ∪ B ⊆ U := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_union_add_card_inter A B
  have hc2 := Finset.card_sdiff_add_card_eq_card hsub
  rw [hAB, Finset.card_singleton, hA,hB] at hc
  rw [← hcomp] at hc2
  have hU : U.card = Fintype.card G * (twoTorsion : Finset G).card := by simp [U]
  omega




















attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d v : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        d d)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G d
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              v v)
            v)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G v
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Eq.{1} Nat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G)
                (@Couret.STROBO2TORS.pairLifts.{p2m_u_0} G inst inst_1 inst_2 d v))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.STROBO2TORS.p2m_local_pairLifts_card_balance

