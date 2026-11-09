-- Prove2me | solution 1 for Couret.STROBO2TORS.paramSupport_parameters_unique
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:03.679863+00:00
-- url     : https://prove2.me/submissions/2d4e8cac-16e3-45dc-8128-498f1586d6d4

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paired_singleton_equal_of_support_eq
import Theorems.Thm_Couret_STROBO2TORS_triple_sum_translate
import Theorems.Thm_Couret_STROBO2TORS_two_point_pair_direction
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]











/-- Unique raw parametrization: singleton a, nonzero H-direction d, nonzero G[3] element v. -/
theorem p2m_local_paramSupport_parameters_unique (a d v t e w : G)
    (hd : d + d = 0) (he : e + e = 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hv : (v + v) + v = 0) (hw : (w + w) + w = 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hs : paramSupport ((a, d), v) = paramSupport ((t, e), w)) :
    a = t ∧ d = e ∧ v = w := by
  have hab := exceptional_param_genuine a v hv hv0
  have htc := exceptional_param_genuine t w hw hw0
  have hat := paired_singleton_equal_of_support_eq a (a + v) d t (t + w) e
    hd he hd0 he0 hab htc hs
  subst t
  obtain ⟨hav, havd, _⟩ := paired_entries_distinct a (a + v) d hd hd0 hab
  obtain ⟨haw, hawe, _⟩ := paired_entries_distinct a (a + w) e he he0 htc
  have hp := congrArg (fun S : Finset G => S.erase a) hs
  change ({a, a + v, (a + v) + d} : Finset G).erase a =
    ({a, a + w, (a + w) + e} : Finset G).erase a at hp
  have hpairs : ({a + v, (a + v) + d} : Finset G) = {a + w, (a + w) + e} := by
    simpa [hav, havd, haw, hawe, Ne.symm hav, Ne.symm havd, Ne.symm haw, Ne.symm hawe] using hp
  have hed := two_point_pair_direction (a + v) (a + w) d e hd hd0 he0 hpairs
  have hm : a + w ∈ ({a + v, (a + v) + d} : Finset G) := by rw [hpairs]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hwv : w = v := by
    rcases hm with h | h
    · exact add_left_cancel h
    · have hwvd : w = v + d := by
        apply add_left_cancel (a := a)
        calc
          a + w = (a + v) + d := h
          _ = a + (v + d) := by abel
      have hk := triple_sum_translate v v v d hd
      rw [hwvd, hk, hv] at hw
      have hz : d = 0 := by simpa using hw
      exact (hd0 hz).elim
  exact ⟨rfl, hed.symm, hwv.symm⟩



section Finite

variable [Fintype G]

























































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a d v t e w : G),
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
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          e e)
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
        @Ne.{p2m_u_0 + 1} G e
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
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
            @Eq.{p2m_u_0 + 1} G
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
                    w w)
                  w)
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
                @Ne.{p2m_u_0 + 1} G w
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
                  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G t e) w)) →
                    And (@Eq.{p2m_u_0 + 1} G a t) (And (@Eq.{p2m_u_0 + 1} G d e) (@Eq.{p2m_u_0 + 1} G v w)) := @_root_.Couret.STROBO2TORS.p2m_local_paramSupport_parameters_unique

