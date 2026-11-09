-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_binary_kernel_genuine_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:06.295825+00:00
-- url     : https://prove2.me/submissions/effd9a36-027c-4ee9-a654-b87bf6e66bb9

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b

set_option autoImplicit false

/-!
RECOH: binary evaluation dichotomy and exact collision reduction.

This module eliminates a manual case split for arbitrary finite banks:
either a nonzero binary kernel exists or the binary evaluation is injective.
In the injective case it records the information-set selection as one
EXPLICIT hypothesis. It does not claim that selection for general rank.

The rank-one case has a separate certified branch and is not duplicated.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- A witnessed common binary kernel produces a real collision of
distinct three-element supports. This works even when k >= r,
so it complements the cardinal-only rank kernel lemma. -/
theorem p2m_local_recoh_binary_kernel_genuine_collision
    {H R : Type*}
    [AddCommGroup H] [CommRing R]
    (k : ℕ)
    (h2 : ∀ a : H, a + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ a b : G,
      bank i (a + b) = bank i a * bank i b)
    (binary : Fin k → H →+ ZMod 2)
    (hzero : ∀ i : Fin k, ∀ a : H,
      binary i a = 0 → bank i (embH a) = 1)
    (kernel : ∃ a : H, a ≠ 0 ∧ ∀ i : Fin k, binary i a = 0)
    (x y z : G) (hcard : ({x, y, z} : Finset G).card = 3) :
    ∃ d : G,
      d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d)) := by
  obtain ⟨a, ha, hker⟩ := kernel
  let d : G := embH a
  have hd0 : d ≠ 0 := by
    intro hd
    apply ha
    apply injH
    simpa [d] using hd
  have hd2 : d + d = 0 := by
    dsimp [d]
    simpa only [map_add, map_zero] using congrArg embH (h2 a)
  have hne : translateSupport ({x, y, z} : Finset G) d ≠
      ({x, y, z} : Finset G) := by
    intro hfixed
    exact hd0 (translateSupport_free_of_card_three
      ({x, y, z} : Finset G) hcard d hd2 hfixed)
  refine ⟨d, hd0, hd2, ?_, ?_, ?_⟩
  · intro hsame
    apply hne
    simpa only [translateSupport_three] using hsame.symm
  · intro q
    have hsq := orderedSquare_translate_of_card_three
      ({x, y, z} : Finset G) hcard d q hd2
    rw [translateSupport_three] at hsq
    exact hsq.symm
  · intro i
    have hu : bank i d = 1 := hzero i a (hker i)
    have hp := recoh_triple_probe_translate (bank i) (hadd i) x y z d
    rw [hu, one_mul] at hp
    exact hp.symm



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {H : Type p2m_u_1}
  {R : Type p2m_u_2} [inst_2 : AddCommGroup.{p2m_u_1} H] [inst_3 : CommRing.{p2m_u_2} R] (k : Nat),
  (∀ (a : H),
      @Eq.{p2m_u_1 + 1} H
        (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} H H H
          (@instHAdd.{p2m_u_1} H
            (@AddCommMagma.toAdd.{p2m_u_1} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} H (@AddCommGroup.toAddCommMonoid.{p2m_u_1} H inst_2)))))
          a a)
        (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_1} H
            (@NegZeroClass.toZero.{p2m_u_1} H
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_2)))))))) →
    ∀
      (embH :
        @AddMonoidHom.{p2m_u_1, p2m_u_0} H G
          (@AddZeroClass.toAddZero.{p2m_u_1} H
            (@AddMonoid.toAddZeroClass.{p2m_u_1} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))),
      @Function.Injective.{p2m_u_1 + 1, p2m_u_0 + 1} H G
          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
            (@AddMonoidHom.{p2m_u_1, p2m_u_0} H G
              (@AddZeroClass.toAddZero.{p2m_u_1} H
                (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
              (@AddZeroClass.toAddZero.{p2m_u_0} G
                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
            H (fun x => G)
            (@AddMonoidHom.instFunLike.{p2m_u_1, p2m_u_0} H G
              (@AddZeroClass.toAddZero.{p2m_u_1} H
                (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
              (@AddZeroClass.toAddZero.{p2m_u_0} G
                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
            embH) →
        ∀ (bank : Fin k → G → R),
          (∀ (i : Fin k) (a b : G),
              @Eq.{p2m_u_2 + 1} R
                (bank i
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    a b))
                (@HMul.hMul.{p2m_u_2, p2m_u_2, p2m_u_2} R R R
                  (@instHMul.{p2m_u_2} R
                    (@Distrib.toMul.{p2m_u_2} R
                      (@instDistribOfSemiring.{p2m_u_2} R
                        (@CommSemiring.toSemiring.{p2m_u_2} R (@CommRing.toCommSemiring.{p2m_u_2} R inst_3)))))
                  (bank i a) (bank i b))) →
            ∀
              (binary :
                Fin k →
                  @AddMonoidHom.{p2m_u_1, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddZeroClass.toAddZero.{p2m_u_1} H
                      (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                        (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                          (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                    (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoid.toAddZeroClass.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoidWithOne.toAddMonoid.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))),
              (∀ (i : Fin k) (a : H),
                  @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
                        (@AddMonoidHom.{p2m_u_1, 0} H
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddZeroClass.toAddZero.{p2m_u_1} H
                            (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                              (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
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
                        (@AddMonoidHom.instFunLike.{p2m_u_1, 0} H
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddZeroClass.toAddZero.{p2m_u_1} H
                            (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                              (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
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
                        (binary i) a)
                      (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@instMulZeroClassOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))) →
                    @Eq.{p2m_u_2 + 1} R
                      (bank i
                        (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
                          (@AddMonoidHom.{p2m_u_1, p2m_u_0} H G
                            (@AddZeroClass.toAddZero.{p2m_u_1} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} H
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                          H (fun x => G)
                          (@AddMonoidHom.instFunLike.{p2m_u_1, p2m_u_0} H G
                            (@AddZeroClass.toAddZero.{p2m_u_1} H
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} H
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                          embH a))
                      (@OfNat.ofNat.{p2m_u_2} R (nat_lit 1)
                        (@One.toOfNat1.{p2m_u_2} R
                          (@AddMonoidWithOne.toOne.{p2m_u_2} R
                            (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_2} R
                              (@Ring.toAddGroupWithOne.{p2m_u_2} R (@CommRing.toRing.{p2m_u_2} R inst_3))))))) →
                (@Exists.{p2m_u_1 + 1} H fun a =>
                    And
                      (@Ne.{p2m_u_1 + 1} H a
                        (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
                          (@Zero.toOfNat0.{p2m_u_1} H
                            (@NegZeroClass.toZero.{p2m_u_1} H
                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_2))))))))
                      (∀ (i : Fin k),
                        @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
                            (@AddMonoidHom.{p2m_u_1, 0} H
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} H
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} H
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
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
                            (@AddMonoidHom.instFunLike.{p2m_u_1, 0} H
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} H
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} H
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_2)))))
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
                            (binary i) a)
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
                                      (ZMod.commRing
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) →
                  ∀ (x y z : G),
                    @Eq.{1} Nat
                        (@Finset.card.{p2m_u_0} G
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1) x
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1) y
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instSingleton.{p2m_u_0} G) z))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      @Exists.{p2m_u_0 + 1} G fun d =>
                        And
                          (@Ne.{p2m_u_0 + 1} G d
                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                              (@Zero.toOfNat0.{p2m_u_0} G
                                (@NegZeroClass.toZero.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                          (And
                            (@Eq.{p2m_u_0 + 1} G
                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                (@instHAdd.{p2m_u_0} G
                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                d d)
                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                (@Zero.toOfNat0.{p2m_u_0} G
                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                            (And
                              (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                  (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                    (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                      (@Finset.instSingleton.{p2m_u_0} G) z)))
                                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                  (@Finset.instInsert.{p2m_u_0} G inst_1)
                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                    (@instHAdd.{p2m_u_0} G
                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                    x d)
                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                      (@instHAdd.{p2m_u_0} G
                                        (@AddCommMagma.toAdd.{p2m_u_0} G
                                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                      y d)
                                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                      (@Finset.instSingleton.{p2m_u_0} G)
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        z d)))))
                              (And
                                (∀ (q : G),
                                  @Eq.{1} Nat
                                    (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                        (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                          (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                            (@Finset.instSingleton.{p2m_u_0} G) z)))
                                      q)
                                    (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                        (@Finset.instInsert.{p2m_u_0} G inst_1)
                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                          (@instHAdd.{p2m_u_0} G
                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                          x d)
                                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                          (@Finset.instInsert.{p2m_u_0} G inst_1)
                                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                            (@instHAdd.{p2m_u_0} G
                                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                            y d)
                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                            (@Finset.instSingleton.{p2m_u_0} G)
                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                              (@instHAdd.{p2m_u_0} G
                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                              z d))))
                                      q))
                                (∀ (i : Fin k),
                                  @Eq.{p2m_u_2 + 1} R
                                    (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_3 (bank i) x y z)
                                    (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_3 (bank i)
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        x d)
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        y d)
                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                        (@instHAdd.{p2m_u_0} G
                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                        z d)))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_binary_kernel_genuine_collision

