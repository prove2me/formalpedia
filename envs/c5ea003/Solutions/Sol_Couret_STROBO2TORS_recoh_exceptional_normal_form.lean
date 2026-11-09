-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exceptional_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:39.709024+00:00
-- url     : https://prove2.me/submissions/b93ed440-64fc-48cd-bdab-4f9e4d92b843

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_sum_translate
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: reconstructing a cardinality-three support from its labelled ordered
square and a fixed bank of individual complex character coefficients.

The observation and the support cardinality are explicit. The classification
used below is the existing STROBO theorem, not an additional hypothesis.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- Normal form for both members of an exceptional collision, including its
unknown two-torsion translation. -/
theorem p2m_local_recoh_exceptional_normal_form (S T : Finset G)
    (he : ExceptionalPartner S T) :
    ∃ a d v u : G, d + d = 0 ∧ d ≠ 0 ∧
      (v + v) + v = 0 ∧ v ≠ 0 ∧ u + u = 0 ∧
      S = paramSupport ((a, d), v) ∧
      T = translateSupport (paramSupport ((a, d), -v)) u := by
  obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := he
  obtain ⟨v, hv, hvb⟩ : ∃ v : G, (v + v) + v = 0 ∧
      (b - a = v ∨ b - a = v + d) := by
    rcases h3 with h | h
    · exact ⟨b - a, h, Or.inl rfl⟩
    · refine ⟨(b - a) + d, ?_, Or.inr ?_⟩
      · calc
          (((b - a) + d) + ((b - a) + d)) + ((b - a) + d) =
              (((b - a) + (b - a)) + (b - a)) + d :=
            triple_sum_translate (b - a) (b - a) (b - a) d hd
          _ = d + d := by rw [h]
          _ = 0 := hd
      · simp [add_assoc, hd]
  have hv0 : v ≠ 0 := by
    intro hv0
    have h2 : (b - a) + (b - a) = 0 := by
      rcases hvb with h | h
      · simp [h, hv0]
      · simpa [h, hv0] using hd
    exact hab ((double_eq_iff_two_torsion a b).mpr h2)
  have hv2 : v + v = -v := eq_neg_of_add_eq_zero_left hv
  refine ⟨a, d, v, u, hd, hd0, hv, hv0, hu, ?_, ?_⟩
  · rw [hs]
    rcases hvb with h | h
    · have hb : b = a + v := by rw [← h]; abel
      simp only [paramSupport, hb]
    · have hb : b = (a + v) + d := by
        calc
          b = a + (b - a) := by abel
          _ = a + (v + d) := by rw [h]
          _ = (a + v) + d := by abel
      have hbd : b + d = a + v := by rw [hb]; simp [add_assoc, hd]
      simp only [paramSupport]
      rw [hbd, hb]
      exact support_swap_last a ((a + v) + d) (a + v)
  · rw [ht]
    congr 1
    have hf : b + b - a = a + -v := by
      rcases hvb with h | h
      · have hb : b = a + v := by rw [← h]; abel
        calc
          b + b - a = a + (v + v) := by rw [hb]; abel
          _ = a + -v := by rw [hv2]
      · have hb : b = (a + v) + d := by
          calc
            b = a + (b - a) := by abel
            _ = a + (v + d) := by rw [h]
            _ = (a + v) + d := by abel
        calc
          b + b - a = (a + (v + v)) + (d + d) := by rw [hb]; abel
          _ = a + -v := by rw [hv2, hd]; simp
    simp only [paramSupport, hf]











end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T →
    @Exists.{p2m_u_0 + 1} G fun a =>
      @Exists.{p2m_u_0 + 1} G fun d =>
        @Exists.{p2m_u_0 + 1} G fun v =>
          @Exists.{p2m_u_0 + 1} G fun u =>
            And
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
                          u u)
                        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                          (@Zero.toOfNat0.{p2m_u_0} G
                            (@NegZeroClass.toZero.{p2m_u_0} G
                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                      (And
                        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S
                          (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                            (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                              (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v)))
                        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                          (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1
                            (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                              (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                                (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                                (@Neg.neg.{p2m_u_0} G
                                  (@NegZeroClass.toNeg.{p2m_u_0} G
                                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                  v)))
                            u))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exceptional_normal_form

