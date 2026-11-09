-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_bank_collision_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:23.63981+00:00
-- url     : https://prove2.me/submissions/ea04ca7c-e90e-4f6c-9670-478789e543d4

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_bank_kernel_or_injective
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_kernel_genuine_collision
import Theorems.Thm_Couret_STROBO2TORS_recoh_pivot_bank_has_genuine_collision
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





/-- Complete conditional lower-bound interface for a common bank:
the binary-kernel case always gives a translated collision;
otherwise an explicitly supplied information set gives a reflected
collision. The remaining mathematical obligation is to remove
the hinfo hypothesis for elementary binary torsion groups. -/
theorem p2m_local_recoh_short_bank_collision_dichotomy
    {H V R : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    [CommRing R]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (h2 : ∀ a : H, a + a = 0)
    (h3 : ∀ a : V, (a + a) + a = 0)
    (embH : H →+ G) (injH : Function.Injective embH)
    (embV : V →+ G) (injV : Function.Injective embV)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ a b : G,
      bank i (a + b) = bank i a * bank i b)
    (hval0 : ∀ i : Fin k, bank i 0 = 1)
    (binary : Fin k → H →+ ZMod 2)
    (hbinary0 : ∀ i : Fin k, ∀ a : H,
      binary i a = 0 → bank i (embH a) = 1)
    (hbinary1 : ∀ i : Fin k, ∀ a : H,
      binary i a ≠ 0 → bank i (embH a) = -1)
    (ternary : Fin k → V →+ ZMod 3)
    (hternary : ∀ i : Fin k, ∀ a : V,
      ternary i a = 0 → bank i (embV a) = 1)
    (hinfo : Function.Injective
        (fun a : H => fun i : Fin k => binary i a) →
      ∃ pivot : Fin r → Fin k,
        Function.Injective pivot ∧
        Function.Surjective
          (fun a : H => fun j : Fin r => binary (pivot j) a))
    (x y z : G) (hcard : ({x, y, z} : Finset G).card = 3) :
    (∃ d : G, d ≠ 0 ∧ d + d = 0 ∧
      ({x, y, z} : Finset G) ≠ {x + d, y + d, z + d} ∧
      (∀ q : G,
        orderedSquare ({x, y, z} : Finset G) q =
          orderedSquare ({x + d, y + d, z + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) x y z =
          recohTripleProbe (bank i) (x + d) (y + d) (z + d))) ∨
    (∃ d v : G, d ≠ 0 ∧ d + d = 0 ∧
      v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ q : G,
        orderedSquare ({0, v, v + d} : Finset G) q =
          orderedSquare ({0, -v, -v + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d))) := by
  rcases recoh_binary_bank_kernel_or_injective k binary with hker | hinj
  · left
    exact recoh_binary_kernel_genuine_collision k h2 embH injH bank hadd
      binary hbinary0 hker x y z hcard
  · right
    obtain ⟨pivot, hpiv, hsurj⟩ := hinfo hinj
    exact recoh_pivot_bank_has_genuine_collision r s k hr hk hcardV
      h2 h3 embH injH embV injV bank hadd hval0 binary pivot
      hpiv hsurj hbinary1 ternary hternary

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2 p2m_u_3
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {H : Type p2m_u_1}
  {V : Type p2m_u_2} {R : Type p2m_u_3} [inst_2 : AddCommGroup.{p2m_u_1} H] [Fintype.{p2m_u_1} H]
  [inst_4 : AddCommGroup.{p2m_u_2} V] [inst_5 : Fintype.{p2m_u_2} V] [inst_6 : CommRing.{p2m_u_3} R] (r s k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r s) →
      @Eq.{1} Nat (@Fintype.card.{p2m_u_2} V inst_5)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
        (∀ (a : H),
            @Eq.{p2m_u_1 + 1} H
              (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} H H H
                (@instHAdd.{p2m_u_1} H
                  (@AddCommMagma.toAdd.{p2m_u_1} H
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} H
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} H
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_1} H inst_2)))))
                a a)
              (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_1} H
                  (@NegZeroClass.toZero.{p2m_u_1} H
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_2)))))))) →
          (∀ (a : V),
              @Eq.{p2m_u_2 + 1} V
                (@HAdd.hAdd.{p2m_u_2, p2m_u_2, p2m_u_2} V V V
                  (@instHAdd.{p2m_u_2} V
                    (@AddCommMagma.toAdd.{p2m_u_2} V
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_2} V
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_2} V
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_2} V inst_4)))))
                  (@HAdd.hAdd.{p2m_u_2, p2m_u_2, p2m_u_2} V V V
                    (@instHAdd.{p2m_u_2} V
                      (@AddCommMagma.toAdd.{p2m_u_2} V
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_2} V
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_2} V
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_2} V inst_4)))))
                    a a)
                  a)
                (@OfNat.ofNat.{p2m_u_2} V (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_2} V
                    (@NegZeroClass.toZero.{p2m_u_2} V
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_2} V
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_2} V
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_2} V
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_2} V inst_4)))))))) →
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
                ∀
                  (embV :
                    @AddMonoidHom.{p2m_u_2, p2m_u_0} V G
                      (@AddZeroClass.toAddZero.{p2m_u_2} V
                        (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                          (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                            (@AddGroup.toSubNegMonoid.{p2m_u_2} V (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                      (@AddZeroClass.toAddZero.{p2m_u_0} G
                        (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))),
                  @Function.Injective.{p2m_u_2 + 1, p2m_u_0 + 1} V G
                      (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_2 + 1, p2m_u_0 + 1}
                        (@AddMonoidHom.{p2m_u_2, p2m_u_0} V G
                          (@AddZeroClass.toAddZero.{p2m_u_2} V
                            (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                              (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                (@AddGroup.toSubNegMonoid.{p2m_u_2} V (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                          (@AddZeroClass.toAddZero.{p2m_u_0} G
                            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                        V (fun x => G)
                        (@AddMonoidHom.instFunLike.{p2m_u_2, p2m_u_0} V G
                          (@AddZeroClass.toAddZero.{p2m_u_2} V
                            (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                              (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                (@AddGroup.toSubNegMonoid.{p2m_u_2} V (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                          (@AddZeroClass.toAddZero.{p2m_u_0} G
                            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                        embV) →
                    ∀ (bank : Fin k → G → R),
                      (∀ (i : Fin k) (a b : G),
                          @Eq.{p2m_u_3 + 1} R
                            (bank i
                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                (@instHAdd.{p2m_u_0} G
                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                a b))
                            (@HMul.hMul.{p2m_u_3, p2m_u_3, p2m_u_3} R R R
                              (@instHMul.{p2m_u_3} R
                                (@Distrib.toMul.{p2m_u_3} R
                                  (@instDistribOfSemiring.{p2m_u_3} R
                                    (@CommSemiring.toSemiring.{p2m_u_3} R
                                      (@CommRing.toCommSemiring.{p2m_u_3} R inst_6)))))
                              (bank i a) (bank i b))) →
                        (∀ (i : Fin k),
                            @Eq.{p2m_u_3 + 1} R
                              (bank i
                                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                  (@Zero.toOfNat0.{p2m_u_0} G
                                    (@NegZeroClass.toZero.{p2m_u_0} G
                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                              (@OfNat.ofNat.{p2m_u_3} R (nat_lit 1)
                                (@One.toOfNat1.{p2m_u_3} R
                                  (@AddMonoidWithOne.toOne.{p2m_u_3} R
                                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_3} R
                                      (@Ring.toAddGroupWithOne.{p2m_u_3} R (@CommRing.toRing.{p2m_u_3} R inst_6))))))) →
                          ∀
                            (binary :
                              Fin k →
                                @AddMonoidHom.{p2m_u_1, 0} H
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
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))),
                            (∀ (i : Fin k) (a : H),
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                        (instOfNatNat (nat_lit 2)))))))))))
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                        (instOfNatNat (nat_lit 2)))))))))))
                                      (binary i) a)
                                    (@OfNat.ofNat.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                                      (@Zero.toOfNat0.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                  @Eq.{p2m_u_3 + 1} R
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
                                                (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                  (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
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
                                                (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                  (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                                        embH a))
                                    (@OfNat.ofNat.{p2m_u_3} R (nat_lit 1)
                                      (@One.toOfNat1.{p2m_u_3} R
                                        (@AddMonoidWithOne.toOne.{p2m_u_3} R
                                          (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_3} R
                                            (@Ring.toAddGroupWithOne.{p2m_u_3} R
                                              (@CommRing.toRing.{p2m_u_3} R inst_6))))))) →
                              (∀ (i : Fin k) (a : H),
                                  @Ne.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (ZMod.commRing
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                          (instOfNatNat (nat_lit 2)))))))))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (ZMod.commRing
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                          (instOfNatNat (nat_lit 2)))))))))))
                                        (binary i) a)
                                      (@OfNat.ofNat.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                                        (@Zero.toOfNat0.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@MulZeroClass.toZero.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@instMulZeroClassOfSemiring.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@CommSemiring.toSemiring.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@CommRing.toCommSemiring.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod.commRing
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                      (instOfNatNat (nat_lit 2)))))))))) →
                                    @Eq.{p2m_u_3 + 1} R
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
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
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
                                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                    (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                                          embH a))
                                      (@Neg.neg.{p2m_u_3} R
                                        (@NegZeroClass.toNeg.{p2m_u_3} R
                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_3} R
                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_3} R
                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_3} R
                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_3} R
                                                  (@Ring.toAddCommGroup.{p2m_u_3} R
                                                    (@CommRing.toRing.{p2m_u_3} R inst_6)))))))
                                        (@OfNat.ofNat.{p2m_u_3} R (nat_lit 1)
                                          (@One.toOfNat1.{p2m_u_3} R
                                            (@AddMonoidWithOne.toOne.{p2m_u_3} R
                                              (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_3} R
                                                (@Ring.toAddGroupWithOne.{p2m_u_3} R
                                                  (@CommRing.toRing.{p2m_u_3} R inst_6)))))))) →
                                ∀
                                  (ternary :
                                    Fin k →
                                      @AddMonoidHom.{p2m_u_2, 0} V
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                        (@AddZeroClass.toAddZero.{p2m_u_2} V
                                          (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                            (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                              (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                                (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                                        (@AddZeroClass.toAddZero.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@AddMonoid.toAddZeroClass.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@AddMonoidWithOne.toAddMonoid.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@Ring.toAddGroupWithOne.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@CommRing.toRing.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (ZMod.commRing
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                        (instOfNatNat (nat_lit 3))))))))))),
                                  (∀ (i : Fin k) (a : V),
                                      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@DFunLike.coe.{p2m_u_2 + 1, p2m_u_2 + 1, 1}
                                            (@AddMonoidHom.{p2m_u_2, 0} V
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@AddZeroClass.toAddZero.{p2m_u_2} V
                                                (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                                  (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                                    (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                                      (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                                              (@AddZeroClass.toAddZero.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@AddMonoid.toAddZeroClass.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@AddMonoidWithOne.toAddMonoid.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@Ring.toAddGroupWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@CommRing.toRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (ZMod.commRing
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))))))))))
                                            V
                                            (fun x =>
                                              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@AddMonoidHom.instFunLike.{p2m_u_2, 0} V
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@AddZeroClass.toAddZero.{p2m_u_2} V
                                                (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                                  (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                                    (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                                      (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                                              (@AddZeroClass.toAddZero.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@AddMonoid.toAddZeroClass.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@AddMonoidWithOne.toAddMonoid.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@Ring.toAddGroupWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@CommRing.toRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (ZMod.commRing
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))))))))))
                                            (ternary i) a)
                                          (@OfNat.ofNat.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (nat_lit 0)
                                            (@Zero.toOfNat0.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@MulZeroClass.toZero.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@instMulZeroClassOfSemiring.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@CommSemiring.toSemiring.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (@CommRing.toCommSemiring.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (ZMod.commRing
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                          (instOfNatNat (nat_lit 3)))))))))) →
                                        @Eq.{p2m_u_3 + 1} R
                                          (bank i
                                            (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_2 + 1, p2m_u_0 + 1}
                                              (@AddMonoidHom.{p2m_u_2, p2m_u_0} V G
                                                (@AddZeroClass.toAddZero.{p2m_u_2} V
                                                  (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                                    (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                                      (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                                        (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                                                (@AddZeroClass.toAddZero.{p2m_u_0} G
                                                  (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                                              V (fun x => G)
                                              (@AddMonoidHom.instFunLike.{p2m_u_2, p2m_u_0} V G
                                                (@AddZeroClass.toAddZero.{p2m_u_2} V
                                                  (@AddMonoid.toAddZeroClass.{p2m_u_2} V
                                                    (@SubNegMonoid.toAddMonoid.{p2m_u_2} V
                                                      (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                                        (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                                                (@AddZeroClass.toAddZero.{p2m_u_0} G
                                                  (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                                              embV a))
                                          (@OfNat.ofNat.{p2m_u_3} R (nat_lit 1)
                                            (@One.toOfNat1.{p2m_u_3} R
                                              (@AddMonoidWithOne.toOne.{p2m_u_3} R
                                                (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_3} R
                                                  (@Ring.toAddGroupWithOne.{p2m_u_3} R
                                                    (@CommRing.toRing.{p2m_u_3} R inst_6))))))) →
                                    ((@Function.Injective.{p2m_u_1 + 1, 1} H
                                          (Fin k → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          fun a i =>
                                          @DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@Ring.toAddGroupWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@CommRing.toRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (ZMod.commRing
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))))))))))
                                            H
                                            (fun x =>
                                              ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@Ring.toAddGroupWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@CommRing.toRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (ZMod.commRing
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))))))))))
                                            (binary i) a) →
                                        @Exists.{1} (Fin r → Fin k) fun pivot =>
                                          And (@Function.Injective.{1, 1} (Fin r) (Fin k) pivot)
                                            (@Function.Surjective.{p2m_u_1 + 1, 1} H
                                              (Fin r →
                                                ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              fun a j =>
                                              @DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@AddMonoidWithOne.toAddMonoid.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (@Ring.toAddGroupWithOne.{0}
                                                            (ZMod
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2))))
                                                            (@CommRing.toRing.{0}
                                                              (ZMod
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2))))
                                                              (ZMod.commRing
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))))))))))
                                                H
                                                (fun x =>
                                                  ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@AddMonoidWithOne.toAddMonoid.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (@Ring.toAddGroupWithOne.{0}
                                                            (ZMod
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2))))
                                                            (@CommRing.toRing.{0}
                                                              (ZMod
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2))))
                                                              (ZMod.commRing
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))))))))))
                                                (binary (pivot j)) a)) →
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
                                          Or
                                            (@Exists.{p2m_u_0 + 1} G fun d =>
                                              And
                                                (@Ne.{p2m_u_0 + 1} G d
                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst))))))))
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
                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                  inst))))))))
                                                  (And
                                                    (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                                                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                        (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                          (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                            (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                                                            z)))
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
                                                          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                            (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                              (@instHAdd.{p2m_u_0} G
                                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                        inst)))))
                                                              z d)))))
                                                    (And
                                                      (∀ (q : G),
                                                        @Eq.{1} Nat
                                                          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                              (@Finset.instInsert.{p2m_u_0} G inst_1) x
                                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                                (@Finset.instInsert.{p2m_u_0} G inst_1) y
                                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                  (Finset.{p2m_u_0} G)
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
                                                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                          inst)))))
                                                                x d)
                                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                                (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                  (@instHAdd.{p2m_u_0} G
                                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                            inst)))))
                                                                  y d)
                                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                  (Finset.{p2m_u_0} G)
                                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                    (@instHAdd.{p2m_u_0} G
                                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                              inst)))))
                                                                    z d))))
                                                            q))
                                                      (∀ (i : Fin k),
                                                        @Eq.{p2m_u_3 + 1} R
                                                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_3} G R
                                                            inst_6 (bank i) x y z)
                                                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_3} G R
                                                            inst_6 (bank i)
                                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                              (@instHAdd.{p2m_u_0} G
                                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                        inst)))))
                                                              x d)
                                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                              (@instHAdd.{p2m_u_0} G
                                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                        inst)))))
                                                              y d)
                                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                              (@instHAdd.{p2m_u_0} G
                                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                        inst)))))
                                                              z d)))))))
                                            (@Exists.{p2m_u_0 + 1} G fun d =>
                                              @Exists.{p2m_u_0 + 1} G fun v =>
                                                And
                                                  (@Ne.{p2m_u_0 + 1} G d
                                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                      (@Zero.toOfNat0.{p2m_u_0} G
                                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                  inst))))))))
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
                                                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                    inst))))))))
                                                    (And
                                                      (@Ne.{p2m_u_0 + 1} G v
                                                        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                          (@Zero.toOfNat0.{p2m_u_0} G
                                                            (@NegZeroClass.toZero.{p2m_u_0} G
                                                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                    G
                                                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                      inst))))))))
                                                      (And
                                                        (@Eq.{p2m_u_0 + 1} G
                                                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                            (@instHAdd.{p2m_u_0} G
                                                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                              (@instHAdd.{p2m_u_0} G
                                                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                        inst)))))
                                                              v v)
                                                            v)
                                                          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                            (@Zero.toOfNat0.{p2m_u_0} G
                                                              (@NegZeroClass.toZero.{p2m_u_0} G
                                                                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                      G
                                                                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                        inst))))))))
                                                        (And
                                                          (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                (@Zero.toOfNat0.{p2m_u_0} G
                                                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                          G
                                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                            G inst)))))))
                                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                                (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                  (Finset.{p2m_u_0} G)
                                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                    (@instHAdd.{p2m_u_0} G
                                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                              inst)))))
                                                                    v d))))
                                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                (@Zero.toOfNat0.{p2m_u_0} G
                                                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                          G
                                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                            G inst)))))))
                                                              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                                (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                                (@Neg.neg.{p2m_u_0} G
                                                                  (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                          G
                                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                            G inst)))))
                                                                  v)
                                                                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                  (Finset.{p2m_u_0} G)
                                                                  (@Finset.instSingleton.{p2m_u_0} G)
                                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                    (@instHAdd.{p2m_u_0} G
                                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                              inst)))))
                                                                    (@Neg.neg.{p2m_u_0} G
                                                                      (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                            G
                                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                              G
                                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                G inst)))))
                                                                      v)
                                                                    d)))))
                                                          (And
                                                            (∀ (q : G),
                                                              @Eq.{1} Nat
                                                                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst
                                                                  inst_1
                                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G
                                                                    (Finset.{p2m_u_0} G)
                                                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                      (@Zero.toOfNat0.{p2m_u_0} G
                                                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                              G
                                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                                G
                                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                  G inst)))))))
                                                                    (@Insert.insert.{p2m_u_0, p2m_u_0} G
                                                                      (Finset.{p2m_u_0} G)
                                                                      (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                                                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                        (Finset.{p2m_u_0} G)
                                                                        (@Finset.instSingleton.{p2m_u_0} G)
                                                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                          (@instHAdd.{p2m_u_0} G
                                                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0}
                                                                                G
                                                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0}
                                                                                  G
                                                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0}
                                                                                    G inst)))))
                                                                          v d))))
                                                                  q)
                                                                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst
                                                                  inst_1
                                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G
                                                                    (Finset.{p2m_u_0} G)
                                                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                      (@Zero.toOfNat0.{p2m_u_0} G
                                                                        (@NegZeroClass.toZero.{p2m_u_0} G
                                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                              G
                                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                                G
                                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                  G inst)))))))
                                                                    (@Insert.insert.{p2m_u_0, p2m_u_0} G
                                                                      (Finset.{p2m_u_0} G)
                                                                      (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                                      (@Neg.neg.{p2m_u_0} G
                                                                        (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                              G
                                                                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                                G
                                                                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                  G inst)))))
                                                                        v)
                                                                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G
                                                                        (Finset.{p2m_u_0} G)
                                                                        (@Finset.instSingleton.{p2m_u_0} G)
                                                                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                          (@instHAdd.{p2m_u_0} G
                                                                            (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0}
                                                                                G
                                                                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0}
                                                                                  G
                                                                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0}
                                                                                    G inst)))))
                                                                          (@Neg.neg.{p2m_u_0} G
                                                                            (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0}
                                                                                G
                                                                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                                  G
                                                                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                                    G
                                                                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                      G inst)))))
                                                                            v)
                                                                          d))))
                                                                  q))
                                                            (∀ (i : Fin k),
                                                              @Eq.{p2m_u_3 + 1} R
                                                                (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_3}
                                                                  G R inst_6 (bank i)
                                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                            G
                                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                              G
                                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                G inst)))))))
                                                                  v
                                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                    (@instHAdd.{p2m_u_0} G
                                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                              inst)))))
                                                                    v d))
                                                                (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_3}
                                                                  G R inst_6 (bank i)
                                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                            G
                                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                              G
                                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                G inst)))))))
                                                                  (@Neg.neg.{p2m_u_0} G
                                                                    (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                          G
                                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                            G
                                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                              G inst)))))
                                                                    v)
                                                                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                                    (@instHAdd.{p2m_u_0} G
                                                                      (@AddCommMagma.toAdd.{p2m_u_0} G
                                                                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G
                                                                              inst)))))
                                                                    (@Neg.neg.{p2m_u_0} G
                                                                      (@NegZeroClass.toNeg.{p2m_u_0} G
                                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0}
                                                                            G
                                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0}
                                                                              G
                                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0}
                                                                                G inst)))))
                                                                      v)
                                                                    d))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_bank_collision_dichotomy

