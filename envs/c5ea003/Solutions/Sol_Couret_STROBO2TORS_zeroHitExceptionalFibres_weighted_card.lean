-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroHitExceptionalFibres_weighted_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:36.681925+00:00
-- url     : https://prove2.me/submissions/fecd5f37-e7bd-44de-8f24-17132655f22d

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalParams_zero_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_injective_on_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_zeroContainingExceptionalSupports_preimage
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]



















theorem exceptionalFibres_zeroContaining_card (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    (F.filter (fun S => 0 ∈ S)).card = 0 ∨ (F.filter (fun S => 0 ∈ S)).card = 2 := by
  have hc := Finset.card_filter_add_card_filter_not (s := F) (fun S : Finset G => 0 ∈ S)
  have hf := exceptionalFibres_member_card F hF
  change (F.filter (fun S => 0 ∈ S)).card + (withoutZero F).card = F.card at hc
  rcases exceptionalFibres_zeroFree_card F hF with h | h <;> omega













theorem zeroContainingExceptionalSupports_card :
    (zeroContainingExceptionalSupports : Finset (Finset G)).card =
      3 * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by
  unfold zeroContainingExceptionalSupports
  rw [exceptionalSupports_eq_params_image, Finset.filter_image]
  have hi : Set.InjOn (paramSupport : (G × G) × G → Finset G)
      ((exceptionalParams : Finset ((G × G) × G)).filter (fun p => 0 ∈ paramSupport p)) := by
    intro p hp q hq heq
    exact paramSupport_injective_on_exceptionalParams
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq
  rw [Finset.card_image_iff.mpr hi, exceptionalParams_zero_card]

theorem zeroHitExceptionalFibres_subset :
    (zeroHitExceptionalFibres : Finset (Finset (Finset G))) ⊆ exceptionalFibres := by
  intro F hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
  exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, hsF⟩



theorem zeroHitExceptionalFibres_member_zeroContaining_card (F : Finset (Finset G))
    (hF : F ∈ (zeroHitExceptionalFibres : Finset (Finset (Finset G)))) :
    (F.filter (fun S => 0 ∈ S)).card = 2 := by
  have hFE := zeroHitExceptionalFibres_subset hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
  have hp : S ∈ zeroContainingExceptionalSupports.filter (fun T : Finset G => squareFibre T = F) :=
    Finset.mem_filter.mpr ⟨hS, hsF⟩
  rw [zeroContainingExceptionalSupports_preimage F hFE] at hp
  have hn := Finset.card_pos.mpr ⟨S, hp⟩
  rcases exceptionalFibres_zeroContaining_card F hFE with h | h <;> omega

theorem p2m_local_zeroHitExceptionalFibres_weighted_card :
    2 * (zeroHitExceptionalFibres : Finset (Finset (Finset G))).card =
      3 * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by
  have hc : (zeroContainingExceptionalSupports : Finset (Finset G)).card =
      2 * (zeroHitExceptionalFibres (G := G)).card := by
    calc
      (zeroContainingExceptionalSupports : Finset (Finset G)).card =
          ∑ F ∈ (zeroHitExceptionalFibres (G := G)),
            ((zeroContainingExceptionalSupports (G := G)).filter
              (fun S => squareFibre S = F)).card :=
        Finset.card_eq_sum_card_image (squareFibre (G := G)) (zeroContainingExceptionalSupports (G := G))
      _ = ∑ _F ∈ (zeroHitExceptionalFibres (G := G)), 2 := by
        apply Finset.sum_congr rfl
        intro F hF
        rw [zeroContainingExceptionalSupports_preimage F (zeroHitExceptionalFibres_subset hF)]
        exact zeroHitExceptionalFibres_member_zeroContaining_card F hF
      _ = (zeroHitExceptionalFibres (G := G)).card * 2 := by simp
      _ = 2 * (zeroHitExceptionalFibres (G := G)).card := Nat.mul_comm _ _
  rw [← hc, zeroContainingExceptionalSupports_card]





































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.zeroHitExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroHitExceptionalFibres_weighted_card

