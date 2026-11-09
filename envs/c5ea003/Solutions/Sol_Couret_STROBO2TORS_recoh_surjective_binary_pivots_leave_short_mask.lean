-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_surjective_binary_pivots_leave_short_mask
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:37.996724+00:00
-- url     : https://prove2.me/submissions/11a49ba1-b182-4c38-84bf-ac0bacf9e610

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
RECOH / STROBO: binary pivot mask counting and ternary subbank kernels.

Conditional interface for the missing mixed-rank selection step.
A surjective rank-r family of binary probes lets one force r signs
simultaneously, leaving fewer than s neutral probes if k < r+s.

The UNCONDITIONAL existence of the pivot family for every full-rank
binary restriction bank is not claimed in this file.
-/

namespace Couret.STROBO2TORS

/-- A surjective r-coordinate binary pivot map allows choosing an input
on which all pivot coordinates equal one. As long as k < r+s, fewer
than s of the k coordinates can vanish on this input.

This is the mixed-rank counting step; surjectivity is an explicit
hypothesis, not a hidden character-existence assumption. -/
theorem p2m_local_recoh_surjective_binary_pivots_leave_short_mask
    {H : Type*} [AddCommGroup H]
    (r s k : ℕ) (hk : k < r + s)
    (bank : Fin k → H →+ ZMod 2)
    (pivot : Fin r → Fin k) (hpiv : Function.Injective pivot)
    (hsurj : Function.Surjective
      (fun d : H => fun j : Fin r => bank (pivot j) d)) :
    ∃ d : H, (∀ j : Fin r, bank (pivot j) d = 1) ∧
      ((Finset.univ : Finset (Fin k)).filter
        (fun i => bank i d = 0)).card < s := by
  classical
  obtain ⟨d, hd⟩ := hsurj (fun _ : Fin r => (1 : ZMod 2))
  have hp : ∀ j : Fin r, bank (pivot j) d = 1 := by
    intro j
    have hj := congrArg (fun f : Fin r → ZMod 2 => f j) hd
    simpa using hj
  let pivots : Finset (Fin k) := Finset.univ.image pivot
  let zeroSet : Finset (Fin k) :=
    Finset.univ.filter (fun i => bank i d = 0)
  have hsubset : zeroSet ⊆ (Finset.univ : Finset (Fin k)) \ pivots := by
    intro i hi
    have hi0 : bank i d = 0 := (Finset.mem_filter.mp hi).2
    have hnot : i ∉ pivots := by
      intro hiP
      obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hiP
      have hi1 : bank i d = 1 := by
        rw [← heq]
        exact hp j
      have hcontra : (0 : ZMod 2) = 1 := hi0.symm.trans hi1
      exact (by decide : (0 : ZMod 2) ≠ 1) hcontra
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
  have hpivotcard : pivots.card = r := by
    dsimp [pivots]
    rw [Finset.card_image_of_injective _ hpiv]
    simp
  have hrem :
      ((Finset.univ : Finset (Fin k)) \ pivots).card = k - r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hpivotcard]
  have hz : zeroSet.card ≤ k - r := by
    calc
      zeroSet.card ≤
        ((Finset.univ : Finset (Fin k)) \ pivots).card :=
          Finset.card_le_card hsubset
      _ = k - r := hrem
  have hrk : r ≤ k := by
    calc
      r = pivots.card := hpivotcard.symm
      _ ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = k := by simp
  refine ⟨d, hp, ?_⟩
  change zeroSet.card < s
  omega



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] (r s k : Nat),
  @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r s) →
    ∀
      (bank :
        Fin k →
          @AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddZeroClass.toAddZero.{p2m_u_0} H
              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
            (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
      (pivot : Fin r → Fin k),
      @Function.Injective.{1, 1} (Fin r) (Fin k) pivot →
        (@Function.Surjective.{p2m_u_0 + 1, 1} H
            (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun d j =>
            @DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
              (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddZeroClass.toAddZero.{p2m_u_0} H
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddMonoidWithOne.toAddMonoid.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
              H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddZeroClass.toAddZero.{p2m_u_0} H
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddMonoidWithOne.toAddMonoid.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
              (bank (pivot j)) d) →
          @Exists.{p2m_u_0 + 1} H fun d =>
            And
              (∀ (j : Fin r),
                @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                    (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddZeroClass.toAddZero.{p2m_u_0} H
                        (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                      (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddZeroClass.toAddZero.{p2m_u_0} H
                        (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                      (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (bank (pivot j)) d)
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                    (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
              (@LT.lt.{0} Nat instLTNat
                (@Finset.card.{0} (Fin k)
                  (@Finset.filter.{0} (Fin k)
                    (fun i =>
                      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                          (@AddMonoidHom.{p2m_u_0, 0} H
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                            (@AddZeroClass.toAddZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddMonoid.toAddZeroClass.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddMonoidWithOne.toAddMonoid.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Ring.toAddGroupWithOne.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@CommRing.toRing.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod.commRing
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                          H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                            (@AddZeroClass.toAddZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddMonoid.toAddZeroClass.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddMonoidWithOne.toAddMonoid.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Ring.toAddGroupWithOne.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@CommRing.toRing.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod.commRing
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                          (bank i) d)
                        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@MulZeroClass.toZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@instMulZeroClassOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@CommRing.toCommSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (fun a =>
                      ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                          (@AddMonoidHom.{p2m_u_0, 0} H
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                            (@AddZeroClass.toAddZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddMonoid.toAddZeroClass.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddMonoidWithOne.toAddMonoid.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Ring.toAddGroupWithOne.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@CommRing.toRing.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod.commRing
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                          H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
                            (@AddZeroClass.toAddZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddMonoid.toAddZeroClass.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddMonoidWithOne.toAddMonoid.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@Ring.toAddGroupWithOne.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@CommRing.toRing.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod.commRing
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                          (bank a) d)
                        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@MulZeroClass.toZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@instMulZeroClassOfSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommSemiring.toSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@CommRing.toCommSemiring.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (@Finset.univ.{0} (Fin k) (Fin.fintype k))))
                s) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_surjective_binary_pivots_leave_short_mask

