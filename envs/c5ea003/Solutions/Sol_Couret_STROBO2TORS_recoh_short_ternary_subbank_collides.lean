-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_ternary_subbank_collides
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:19.89442+00:00
-- url     : https://prove2.me/submissions/3c8f8bc3-0a94-4e0f-9add-729ffe8fd08f

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_order_three_reflection_same_square
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_reflection_of_cancel
import Theorems.Thm_Couret_STROBO2TORS_recoh_reflection_supports_distinct
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_ternary_bank_has_kernel
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_torsion_probe_equal_iff_trivial
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



/-- Conditional mixed-rank collision: if every probe either has
negative value on a nontrivial involution d or belongs to a selected
ternary subbank of length t<s, the latter subbank has a common
nonzero three-torsion kernel vector, producing a real reflected collision.

The missing global theorem must PROVE the existence of such a d and
such a selection for EVERY bank of size k<r+s. -/
theorem p2m_local_recoh_short_ternary_subbank_collides
    {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    (s t k : ℕ) (hcard : Fintype.card A = 3 ^ s) (ht : t < s)
    (h3 : ∀ a : A, (a + a) + a = 0)
    (emb : A →+ G) (hemb : Function.Injective emb)
    (d : G) (hd0 : d ≠ 0) (hd2 : d + d = 0)
    (bank : Fin k → G → R)
    (hadd : ∀ i : Fin k, ∀ x y : G,
      bank i (x + y) = bank i x * bank i y)
    (hzero : ∀ i : Fin k, bank i 0 = 1)
    (selected : Fin t → Fin k)
    (hcover : ∀ i : Fin k,
      bank i d = -1 ∨ ∃ j : Fin t, i = selected j)
    (bits : Fin t → A →+ ZMod 3)
    (hcompat : ∀ j : Fin t, ∀ a : A,
      bits j a = 0 → bank (selected j) (emb a) = 1) :
    ∃ v : G, v ≠ 0 ∧ (v + v) + v = 0 ∧
      ({0, v, v + d} : Finset G) ≠ {0, -v, -v + d} ∧
      (∀ q : G,
        orderedSquare ({0, v, v + d} : Finset G) q =
          orderedSquare ({0, -v, -v + d} : Finset G) q) ∧
      (∀ i : Fin k,
        recohTripleProbe (bank i) 0 v (v + d) =
          recohTripleProbe (bank i) 0 (-v) (-v + d)) := by
  obtain ⟨a, ha, hker⟩ :=
    recoh_short_ternary_bank_has_kernel s t hcard ht bits
  let v : G := emb a
  have hv0 : v ≠ 0 := by
    intro hz
    apply ha
    apply hemb
    simpa [v] using hz
  have hv3 : (v + v) + v = 0 := by
    dsimp [v]
    simpa only [map_add, map_zero] using congrArg emb (h3 a)
  have hmask : ∀ i : Fin k,
      bank i d = -1 ∨ bank i v = bank i (-v) := by
    intro i
    rcases hcover i with hminus | ⟨j, hj⟩
    · exact Or.inl hminus
    · subst i
      apply Or.inr
      apply (recoh_three_torsion_probe_equal_iff_trivial
        (bank (selected j)) (hadd (selected j))
        (hzero (selected j)) v hv3).mpr
      exact hcompat j a (hker j)
  refine ⟨v, hv0, hv3,
    recoh_reflection_supports_distinct v d hv0 hv3 hd2,
    recoh_order_three_reflection_same_square v d hv0 hv3 hd0 hd2, ?_⟩
  intro i
  exact recoh_probe_reflection_of_cancel
    (bank i) (hadd i) v d (hmask i)

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {A : Type p2m_u_1}
  {R : Type p2m_u_2} [inst_2 : AddCommGroup.{p2m_u_1} A] [inst_3 : Fintype.{p2m_u_1} A] [inst_4 : CommRing.{p2m_u_2} R]
  (s t k : Nat),
  @Eq.{1} Nat (@Fintype.card.{p2m_u_1} A inst_3)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
    @LT.lt.{0} Nat instLTNat t s →
      (∀ (a : A),
          @Eq.{p2m_u_1 + 1} A
            (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} A A A
              (@instHAdd.{p2m_u_1} A
                (@AddCommMagma.toAdd.{p2m_u_1} A
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} A
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} A
                      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} A inst_2)))))
              (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} A A A
                (@instHAdd.{p2m_u_1} A
                  (@AddCommMagma.toAdd.{p2m_u_1} A
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} A
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} A
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_1} A inst_2)))))
                a a)
              a)
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
            ∀ (d : G),
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
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      d d)
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
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
                                  (@CommSemiring.toSemiring.{p2m_u_2} R
                                    (@CommRing.toCommSemiring.{p2m_u_2} R inst_4)))))
                            (bank i x) (bank i y))) →
                      (∀ (i : Fin k),
                          @Eq.{p2m_u_2 + 1} R
                            (bank i
                              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                (@Zero.toOfNat0.{p2m_u_0} G
                                  (@NegZeroClass.toZero.{p2m_u_0} G
                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                            (@OfNat.ofNat.{p2m_u_2} R (nat_lit 1)
                              (@One.toOfNat1.{p2m_u_2} R
                                (@AddMonoidWithOne.toOne.{p2m_u_2} R
                                  (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_2} R
                                    (@Ring.toAddGroupWithOne.{p2m_u_2} R (@CommRing.toRing.{p2m_u_2} R inst_4))))))) →
                        ∀ (selected : Fin t → Fin k),
                          (∀ (i : Fin k),
                              Or
                                (@Eq.{p2m_u_2 + 1} R (bank i d)
                                  (@Neg.neg.{p2m_u_2} R
                                    (@NegZeroClass.toNeg.{p2m_u_2} R
                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_2} R
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_2} R
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_2} R
                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_2} R
                                              (@Ring.toAddCommGroup.{p2m_u_2} R
                                                (@CommRing.toRing.{p2m_u_2} R inst_4)))))))
                                    (@OfNat.ofNat.{p2m_u_2} R (nat_lit 1)
                                      (@One.toOfNat1.{p2m_u_2} R
                                        (@AddMonoidWithOne.toOne.{p2m_u_2} R
                                          (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_2} R
                                            (@Ring.toAddGroupWithOne.{p2m_u_2} R
                                              (@CommRing.toRing.{p2m_u_2} R inst_4))))))))
                                (@Exists.{1} (Fin t) fun j => @Eq.{1} (Fin k) i (selected j))) →
                            ∀
                              (bits :
                                Fin t →
                                  @AddMonoidHom.{p2m_u_1, 0} A
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (@AddZeroClass.toAddZero.{p2m_u_1} A
                                      (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                        (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                          (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                            (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))))),
                              (∀ (j : Fin t) (a : A),
                                  @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                      (@DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, 1}
                                        (@AddMonoidHom.{p2m_u_1, 0} A
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@AddZeroClass.toAddZero.{p2m_u_1} A
                                            (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                              (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                                (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                                  (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (ZMod.commRing
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                          (instOfNatNat (nat_lit 3)))))))))))
                                        A (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                        (@AddMonoidHom.instFunLike.{p2m_u_1, 0} A
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@AddZeroClass.toAddZero.{p2m_u_1} A
                                            (@AddMonoid.toAddZeroClass.{p2m_u_1} A
                                              (@SubNegMonoid.toAddMonoid.{p2m_u_1} A
                                                (@AddGroup.toSubNegMonoid.{p2m_u_1} A
                                                  (@AddCommGroup.toAddGroup.{p2m_u_1} A inst_2)))))
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
                                                      (ZMod
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      (ZMod.commRing
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                          (instOfNatNat (nat_lit 3)))))))))))
                                        (bits j) a)
                                      (@OfNat.ofNat.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                                        (@Zero.toOfNat0.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@MulZeroClass.toZero.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@instMulZeroClassOfSemiring.{0}
                                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@CommSemiring.toSemiring.{0}
                                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@CommRing.toCommSemiring.{0}
                                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (ZMod.commRing
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                      (instOfNatNat (nat_lit 3)))))))))) →
                                    @Eq.{p2m_u_2 + 1} R
                                      (bank (selected j)
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
                                              (@Ring.toAddGroupWithOne.{p2m_u_2} R
                                                (@CommRing.toRing.{p2m_u_2} R inst_4))))))) →
                                @Exists.{p2m_u_0 + 1} G fun v =>
                                  And
                                    (@Ne.{p2m_u_0 + 1} G v
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
                                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                            (@instHAdd.{p2m_u_0} G
                                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                            v v)
                                          v)
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
                                            (@Finset.instInsert.{p2m_u_0} G inst_1)
                                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                              (@Zero.toOfNat0.{p2m_u_0} G
                                                (@NegZeroClass.toZero.{p2m_u_0} G
                                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instSingleton.{p2m_u_0} G)
                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                  (@instHAdd.{p2m_u_0} G
                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                  v d))))
                                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                            (@Finset.instInsert.{p2m_u_0} G inst_1)
                                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                              (@Zero.toOfNat0.{p2m_u_0} G
                                                (@NegZeroClass.toZero.{p2m_u_0} G
                                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                                              (@Neg.neg.{p2m_u_0} G
                                                (@NegZeroClass.toNeg.{p2m_u_0} G
                                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                v)
                                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                (@Finset.instSingleton.{p2m_u_0} G)
                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                  (@instHAdd.{p2m_u_0} G
                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                  (@Neg.neg.{p2m_u_0} G
                                                    (@NegZeroClass.toNeg.{p2m_u_0} G
                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                    v)
                                                  d)))))
                                        (And
                                          (∀ (q : G),
                                            @Eq.{1} Nat
                                              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))))
                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                    (@Finset.instInsert.{p2m_u_0} G inst_1) v
                                                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                      (@Finset.instSingleton.{p2m_u_0} G)
                                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                        (@instHAdd.{p2m_u_0} G
                                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                        v d))))
                                                q)
                                              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                                                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                  (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                    (@Zero.toOfNat0.{p2m_u_0} G
                                                      (@NegZeroClass.toZero.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))))
                                                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                    (@Finset.instInsert.{p2m_u_0} G inst_1)
                                                    (@Neg.neg.{p2m_u_0} G
                                                      (@NegZeroClass.toNeg.{p2m_u_0} G
                                                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                inst)))))
                                                      v)
                                                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                                      (@Finset.instSingleton.{p2m_u_0} G)
                                                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                        (@instHAdd.{p2m_u_0} G
                                                          (@AddCommMagma.toAdd.{p2m_u_0} G
                                                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                        (@Neg.neg.{p2m_u_0} G
                                                          (@NegZeroClass.toNeg.{p2m_u_0} G
                                                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                                    inst)))))
                                                          v)
                                                        d))))
                                                q))
                                          (∀ (i : Fin k),
                                            @Eq.{p2m_u_2 + 1} R
                                              (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_4
                                                (bank i)
                                                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                  (@Zero.toOfNat0.{p2m_u_0} G
                                                    (@NegZeroClass.toZero.{p2m_u_0} G
                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                              inst)))))))
                                                v
                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                  (@instHAdd.{p2m_u_0} G
                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                  v d))
                                              (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_2} G R inst_4
                                                (bank i)
                                                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                                                  (@Zero.toOfNat0.{p2m_u_0} G
                                                    (@NegZeroClass.toZero.{p2m_u_0} G
                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G
                                                              inst)))))))
                                                (@Neg.neg.{p2m_u_0} G
                                                  (@NegZeroClass.toNeg.{p2m_u_0} G
                                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                  v)
                                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                                  (@instHAdd.{p2m_u_0} G
                                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                                  (@Neg.neg.{p2m_u_0} G
                                                    (@NegZeroClass.toNeg.{p2m_u_0} G
                                                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                                    v)
                                                  d)))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_ternary_subbank_collides

