-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_bank_collision_of_binary_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:57.660366+00:00
-- url     : https://prove2.me/submissions/c07bf280-2a86-4263-bdbc-7b726407680a

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_bank_collision_dichotomy
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4

set_option autoImplicit false

/-! Structural composition for elementary abelian binary torsion.
The general conditional theorem is preserved; this corollary discharges
its information-set obligation from exponent two and cardinality.
It does not establish the global optimal-bank formula.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The short-bank collision dichotomy without an information-set assumption. -/
theorem p2m_local_recoh_short_bank_collision_of_binary_card
    {H V R : Type*}
    [AddCommGroup H] [Fintype H]
    [AddCommGroup V] [Fintype V]
    [CommRing R]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcardV : Fintype.card V = 3 ^ s)
    (hcardH : Fintype.card H = 2 ^ r)
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
  exact recoh_short_bank_collision_dichotomy r s k hr hk hcardV h2 h3
    embH injH embV injV bank hadd hval0 binary hbinary0 hbinary1
    ternary hternary
    (recoh_binary_information_set_of_card r k h2 hcardH binary)
    x y z hcard

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2 p2m_u_3
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {H : Type p2m_u_1}
  {V : Type p2m_u_2} {R : Type p2m_u_3} [inst_2 : AddCommGroup.{p2m_u_1} H] [inst_3 : Fintype.{p2m_u_1} H]
  [inst_4 : AddCommGroup.{p2m_u_2} V] [inst_5 : Fintype.{p2m_u_2} V] [inst_6 : CommRing.{p2m_u_3} R] (r s k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r s) →
      @Eq.{1} Nat (@Fintype.card.{p2m_u_2} V inst_5)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
        @Eq.{1} Nat (@Fintype.card.{p2m_u_1} H inst_3)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
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
                                  (@AddGroup.toSubNegMonoid.{p2m_u_2} V
                                    (@AddCommGroup.toAddGroup.{p2m_u_2} V inst_4)))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
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
                                        (@Ring.toAddGroupWithOne.{p2m_u_3} R
                                          (@CommRing.toRing.{p2m_u_3} R inst_6))))))) →
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
                                              (@DivisionRing.toRing.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@Field.toDivisionRing.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (@ZMod.instField
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    Nat.fact_prime_two))))))))),
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
                                                    (@DivisionRing.toRing.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@Field.toDivisionRing.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@ZMod.instField
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          Nat.fact_prime_two)))))))))
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
                                                    (@DivisionRing.toRing.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@Field.toDivisionRing.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@ZMod.instField
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          Nat.fact_prime_two)))))))))
                                        (binary i) a)
                                      (@OfNat.ofNat.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                                        (@Zero.toOfNat0.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@MulZeroClass.toZero.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@instMulZeroClassOfSemiring.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@DivisionSemiring.toSemiring.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@Semifield.toDivisionSemiring.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (@Field.toSemifield.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@ZMod.instField
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      Nat.fact_prime_two)))))))) →
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@DivisionRing.toRing.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@Field.toDivisionRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (@ZMod.instField
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            Nat.fact_prime_two)))))))))
                                          H
                                          (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@DivisionRing.toRing.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        (@Field.toDivisionRing.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (@ZMod.instField
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            Nat.fact_prime_two)))))))))
                                          (binary i) a)
                                        (@OfNat.ofNat.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (nat_lit 0)
                                          (@Zero.toOfNat0.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@MulZeroClass.toZero.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@instMulZeroClassOfSemiring.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@DivisionSemiring.toSemiring.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (@Semifield.toDivisionSemiring.{0}
                                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@Field.toSemifield.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@ZMod.instField
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        Nat.fact_prime_two)))))))) →
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
                                                    (@DivisionRing.toRing.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@Field.toDivisionRing.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@ZMod.instField
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                          Nat.fact_prime_three))))))))),
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@Ring.toAddGroupWithOne.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@DivisionRing.toRing.{0}
                                                            (ZMod
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3))))
                                                            (@Field.toDivisionRing.{0}
                                                              (ZMod
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))))
                                                              (@ZMod.instField
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3)))
                                                                Nat.fact_prime_three)))))))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@Ring.toAddGroupWithOne.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@DivisionRing.toRing.{0}
                                                            (ZMod
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3))))
                                                            (@Field.toDivisionRing.{0}
                                                              (ZMod
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))))
                                                              (@ZMod.instField
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3)))
                                                                Nat.fact_prime_three)))))))))
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
                                                    (@DivisionSemiring.toSemiring.{0}
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (@Semifield.toDivisionSemiring.{0}
                                                        (ZMod
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@Field.toSemifield.{0}
                                                          (ZMod
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@ZMod.instField
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))
                                                            Nat.fact_prime_three)))))))) →
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
                                                                    d))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_bank_collision_of_binary_card

