-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeSquareFibre_param_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:22.724031+00:00
-- url     : https://prove2.me/submissions/3d6bfe27-afc8-4f17-9714-cfbb9fa428b8

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paired_zeroFreeSquareFibre_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_ge_two
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]











theorem p2m_local_zeroFreeSquareFibre_param_card (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (zeroFreeSquareFibre (paramSupport ((a, d), v))).card =
      if a + a = 0 ∨ (a + v) + (a + v) = 0 ∨ (a - v) + (a - v) = 0
      then 2 * (twoTorsion : Finset G).card - 2 else 2 * (twoTorsion : Finset G).card := by
  have hneg := three_torsion_neg v hv
  have hneg0 : -v ≠ 0 := neg_ne_zero.mpr hv0
  have h2 := three_torsion_double_eq_neg v hv
  have href : (a + v) + (a + v) - a = a + (-v) := by
    calc
      (a + v) + (a + v) - a = a + (v + v) := by abel
      _ = a + (-v) := by rw [h2]
  have h3 : (((a + v) - a) + ((a + v) - a)) + ((a + v) - a) = 0 ∨
      (((a + v) - a) + ((a + v) - a)) + ((a + v) - a) = d := by
    left; simpa using hv
  have hc := paired_zeroFreeSquareFibre_card a (a + v) d hd hd0
    (exceptional_param_genuine a v hv hv0)
  rw [if_pos h3, href] at hc
  change (zeroFreeSquareFibre (paramSupport ((a, d), v))).card =
    ((twoTorsion : Finset G).card - (paramSupport ((a, d), v) ∩ twoTorsion).card) +
    ((twoTorsion : Finset G).card - (paramSupport ((a, d), -v) ∩ twoTorsion).card) at hc
  rw [paramSupport_inter_twoTorsion_card a d v hd hd0 hv hv0,
    paramSupport_inter_twoTorsion_card a d (-v) hd hd0 hneg hneg0] at hc
  have hab := exceptional_param_genuine a v hv hv0
  have hac := exceptional_param_genuine a (-v) hneg hneg0
  have hbc : (a + v) + (a + v) ≠ (a + (-v)) + (a + (-v)) := by
    have h := exceptional_param_genuine (a + v) v hv hv0
    have hf : (a + v) + v = a + (-v) := by rw [add_assoc, h2]
    rwa [hf] at h
  have hh := twoTorsion_card_ge_two d hd hd0
  simp only [sub_eq_add_neg] at ⊢
  by_cases ha : a + a = 0 <;>
    by_cases hb : (a + v) + (a + v) = 0 <;>
    by_cases hr : (a + (-v)) + (a + (-v)) = 0
  all_goals simp only [ha, hb, hr, if_true, if_false, true_or, false_or, or_true, or_false] at hc ⊢
  all_goals first
    | exact (hab (ha.trans hb.symm)).elim
    | exact (hac (ha.trans hr.symm)).elim
    | exact (hbc (hb.trans hr.symm)).elim
    | omega



































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d v : G),
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
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.zeroFreeSquareFibre.{p2m_u_0} G inst inst_1 inst_2
                (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                  (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                    v))))
            (@ite.{1} Nat
              (Or
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    a a)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (Or
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
                        a v)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))))
              (@instDecidableOr
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    a a)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (Or
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
                        a v)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
                (inst_1
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    a a)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (@instDecidableOr
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
                        a v)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (inst_1
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
                        a v)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (inst_1
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a v))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeSquareFibre_param_card

