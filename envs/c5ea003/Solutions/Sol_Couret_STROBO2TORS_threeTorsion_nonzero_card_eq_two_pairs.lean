-- Prove2me | solution 1 for Couret.STROBO2TORS.threeTorsion_nonzero_card_eq_two_pairs
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:34.530599+00:00
-- url     : https://prove2.me/submissions/f812fd6a-31bf-4412-9f07-f2328cc1b61a

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_preimage
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Nonzero three-torsion cannot also be two-torsion. -/
theorem three_torsion_not_two (v : G) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    v + v ≠ 0 := by
  intro h
  rw [h] at hv
  exact hv0 (by simpa using hv)













section Finite

variable [Fintype G]



















































theorem three_torsion_neg_ne (v : G) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    v ≠ -v := by
  intro h
  apply three_torsion_not_two v hv hv0
  calc
    v + v = v + (-v) := congrArg (fun x => v + x) h
    _ = 0 := by simp



theorem threeSignPairs_member_card (P : Finset G)
    (hP : P ∈ (threeSignPairs : Finset (Finset G))) : P.card = 2 := by
  obtain ⟨v, hv, hp⟩ := Finset.mem_image.mp hP
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  have hv3 := (mem_threeTorsion v).mp (Finset.mem_erase.mp hv).2
  rw [← hp]
  simp [three_torsion_neg_ne v hv3 hv0]

theorem p2m_local_threeTorsion_nonzero_card_eq_two_pairs :
    (threeTorsion : Finset G).card - 1 = 2 * (threeSignPairs : Finset (Finset G)).card := by
  have h0 : (0 : G) ∈ threeTorsion := (mem_threeTorsion 0).mpr (by simp)
  calc
    (threeTorsion : Finset G).card - 1 = ((threeTorsion : Finset G).erase 0).card :=
      (Finset.card_erase_of_mem h0).symm
    _ = ∑ P ∈ (threeSignPairs : Finset (Finset G)),
        (((threeTorsion : Finset G).erase 0).filter (fun w => ({w, -w} : Finset G) = P)).card :=
      Finset.card_eq_sum_card_image (fun v : G => ({v, -v} : Finset G)) (threeTorsion.erase 0)
    _ = ∑ _P ∈ (threeSignPairs : Finset (Finset G)), 2 := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [threeSignPairs_preimage P hP]
      exact threeSignPairs_member_card P hP
    _ = (threeSignPairs : Finset (Finset G)).card * 2 := by simp
    _ = 2 * (threeSignPairs : Finset (Finset G)).card := Nat.mul_comm _ _































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_threeTorsion_nonzero_card_eq_two_pairs

