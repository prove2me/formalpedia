-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_binary_bank_collides
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:56:57.788644+00:00
-- url     : https://prove2.me/submissions/4c97b0ee-5913-4cc0-a5d6-3d1455e631ba

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_binary_bank_has_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b

set_option autoImplicit false

/-!
RECOH: bridge from rank-kernel witnesses to actual triple collisions.

This file contains only conditional lower-bound interfaces.
It does not assert the unrestricted sharp bound r+s, nor
the existence of the requisite spanning H-restrictions.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Fewer than r compatible binary character probes leave a genuine
two-torsion translation of EVERY three-point support indistinguishable.
The additive bit encodings and their compatibility are explicit assumptions. -/
theorem p2m_local_recoh_short_binary_bank_collides
    {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    (r k : ℕ) (hcard : Fintype.card A = 2 ^ r) (hk : k < r)
    (h2 : ∀ a : A, a + a = 0)
    (emb : A →+ G) (hemb : Function.Injective emb)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ x y : G,
      bank i (x + y) = bank i x * bank i y)
    (bits : Fin k → A →+ ZMod 2)
    (hcompat : ∀ i : Fin k, ∀ a : A,
      bits i a = 0 → bank i (emb a) = 1)
    (x y z : G)
    (ht : ({x, y, z} : Finset G).card = 3) :
    ∃ d : G,
      d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d)) := by
  obtain ⟨a, ha, hker⟩ :=
    recoh_short_binary_bank_has_kernel r k hcard hk bits
  let d : G := emb a
  have hd0 : d ≠ 0 := by
    intro hz
    apply ha
    apply hemb
    simpa [d] using hz
  have hd2 : d + d = 0 := by
    dsimp [d]
    simpa only [map_add, map_zero] using congrArg emb (h2 a)
  have hne : translateSupport ({x, y, z} : Finset G) d ≠
      ({x, y, z} : Finset G) := by
    intro hfixed
    exact hd0 (translateSupport_free_of_card_three
      ({x, y, z} : Finset G) ht d hd2 hfixed)
  refine ⟨d, hd0, hd2, ?_, ?_, ?_⟩
  · intro hsame
    apply hne
    simpa only [translateSupport_three] using hsame.symm
  · intro q
    have hsq := orderedSquare_translate_of_card_three
      ({x, y, z} : Finset G) ht d q hd2
    rw [translateSupport_three] at hsq
    exact hsq.symm
  · intro i
    have hunit : bank i d = 1 := hcompat i a (hker i)
    have hp := recoh_triple_probe_translate (bank i) (hadd i) x y z d
    rw [hunit, one_mul] at hp
    exact hp.symm



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {A : Type p2m_u_1}
  {R : Type p2m_u_2} [inst_2 : AddCommGroup.{p2m_u_1} A] [inst_3 : Fintype.{p2m_u_1} A] [inst_4 : CommRing.{p2m_u_2} R]
  (r k : Nat),
  @Eq.{1} Nat (@Fintype.card.{p2m_u_1} A inst_3)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    @LT.lt.{0} Nat instLTNat k r →
      (∀ (a : A),
          @Eq.{p2m_u_1 + 1} A
            (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} A A A
              (@instHAdd.{p2m_u_1} A
                (@AddCommMagma.toAdd.{p2m_u_1} A
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} A
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} A
                      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} A inst_2)))))
              a a)
            (@OfNat.ofNat.{p2m_u_1} A (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_1} A
                (@NegZeroClass.toZero.{p2m_u_1} A
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} A
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} A
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} A
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} A inst_2)))))))) →
        ∀
          (emb :
            @AddMonoidHom.{p2m_u_1, p2m_u_0} A G
              (@AddZeroClass.toAddZero.{p2m_u_1} A
                (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                    (@AddGroup.toSubNegMonoid.{p2m_u_1} A (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
              (@AddZeroClass.toAddZero.{p2m_u_0} G
                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))),
          @Function.Injective.{p2m_u_1 + 1, p2m_u_0 + 1} A G
              (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
                (@AddMonoidHom.{p2m_u_1, p2m_u_0} A G
                  (@AddZeroClass.toAddZero.{p2m_u_1} A
                    (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                      (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                        (@AddGroup.toSubNegMonoid.{p2m_u_1} A (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                A (fun x => G)
                (@AddMonoidHom.instFunLike.{p2m_u_1, p2m_u_0} A G
                  (@AddZeroClass.toAddZero.{p2m_u_1} A
                    (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                      (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                        (@AddGroup.toSubNegMonoid.{p2m_u_1} A (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                emb) →
            ∀ (bank : Fin k → G → R),
              (∀ (i : Fin k) (x y : G),
                  @Eq.{p2m_u_2 + 1} R
                    (bank i
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        x y))
                    (@HMul.hMul.{p2m_u_2, p2m_u_2, p2m_u_2} R R R
                      (@instHMul.{p2m_u_2} R
                        (@Distrib.toMul.{p2m_u_2} R
                          (@instDistribOfSemiring.{p2m_u_2} R
                            (@CommSemiring.toSemiring.{p2m_u_2} R (@CommRing.toCommSemiring.{p2m_u_2} R inst_4)))))
                      (bank i x) (bank i y))) →
                ∀
                  (bits :
                    Fin k →
                      @AddMonoidHom.{p2m_u_1, 0} A (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddZeroClass.toAddZero.{p2m_u_1} A
                          (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                            (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                              (@AddGroup.toSubNegMonoid.{p2m_u_1} A (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))),
                  (∀ (i : Fin k) (a : A),
                      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
                            (@AddMonoidHom.{p2m_u_1, 0} A
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} A
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                            A (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddMonoidHom.instFunLike.{p2m_u_1, 0} A
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} A
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                            (bits i) a)
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
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))) →
                        @Eq.{p2m_u_2 + 1} R
                          (bank i
                            (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
                              (@AddMonoidHom.{p2m_u_1, p2m_u_0} A G
                                (@AddZeroClass.toAddZero.{p2m_u_1} A
                                  (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                    (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                      (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                        (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
                                (@AddZeroClass.toAddZero.{p2m_u_0} G
                                  (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                              A (fun x => G)
                              (@AddMonoidHom.instFunLike.{p2m_u_1, p2m_u_0} A G
                                (@AddZeroClass.toAddZero.{p2m_u_1} A
                                  (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                    (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                      (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                        (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
                                (@AddZeroClass.toAddZero.{p2m_u_0} G
                                  (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                              emb a))
                          (@OfNat.ofNat.{p2m_u_2} R (nat_lit 1)
                            (@One.toOfNat1.{p2m_u_2} R
                              (@AddMonoidWithOne.toOne.{p2m_u_2} R
                                (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_2} R
                                  (@Ring.toAddGroupWithOne.{p2m_u_2} R (@CommRing.toRing.{p2m_u_2} R inst_4))))))) →
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
                                      (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_4 (bank i) x y
                                        z)
                                      (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_4 (bank i)
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
                                          z d)))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_binary_bank_collides

