-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_third_probe_separates_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:41.173546+00:00
-- url     : https://prove2.me/submissions/fe28aca9-5fdd-44c9-8078-e0cd6c08f146

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
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
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









theorem recoh_character_ne_zero (chi : AddChar G ℂ) (x : G) : chi x ≠ 0 := by
  intro hx
  have h := chi.map_add_eq_mul x (-x)
  simp [hx] at h

/-- A third-primary bank is useful precisely through its restrictions to the
two- and three-torsion subgroups. -/
theorem p2m_local_recoh_third_probe_separates_exceptional
    (chi : AddChar G ℂ) (a d v u : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (hcd : chi d = 1) (hcu : chi u = 1) (hcv : chi v ≠ 1) :
    recohSupportProbe chi (paramSupport ((a, d), v)) ≠
      recohSupportProbe chi (translateSupport (paramSupport ((a, d), -v)) u) := by
  have hnv : ((-v + -v) + -v) = 0 := by
    calc
      (-v + -v) + -v = -((v + v) + v) := by abel
      _ = 0 := by rw [hv]; simp
  have hnv0 : -v ≠ 0 := neg_ne_zero.mpr hv0
  have hs3 := paramSupport_card a d v hd hd0 hv hv0
  have ht3 := paramSupport_card a d (-v) hd hd0 hnv hnv0
  obtain ⟨hab, hac, hbc⟩ := displayed_three_distinct a (a + v) ((a + v) + d) hs3
  obtain ⟨hab', hac', hbc'⟩ := displayed_three_distinct a (a + -v) ((a + -v) + d) ht3
  rw [recoh_support_probe_translate, hcu, one_mul]
  change recohSupportProbe chi {a, a + v, (a + v) + d} ≠
    recohSupportProbe chi {a, a + -v, (a + -v) + d}
  rw [recoh_support_probe_three chi _ _ _ hab hac hbc,
    recoh_support_probe_three chi _ _ _ hab' hac' hbc']
  simp only [chi.map_add_eq_mul, hcd, mul_one]
  intro heq
  have heq' : chi a * (chi v - chi (-v)) = 0 := by
    linear_combination (1 / 2 : ℂ) * heq
  have hvn : chi v = chi (-v) := sub_eq_zero.mp
    ((mul_eq_zero.mp heq').resolve_left (recoh_character_ne_zero chi a))
  have h2 : chi v * chi v = 1 := by
    rw [hvn]
    have h := chi.map_add_eq_mul v (-v)
    simpa [hvn] using h.symm
  have h3 : (chi v * chi v) * chi v = 1 := by
    simpa only [chi.map_add_eq_mul, hv, AddChar.map_zero_eq_one] using
      (chi.map_add_eq_mul (v + v) v).symm
  rw [h2, one_mul] at h3
  exact hcv h3







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (a d v u : G),
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
          @Eq.{1} Complex
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddChar.{p2m_u_0, 0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                G (fun x => Complex)
                (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                chi d)
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
            @Eq.{1} Complex
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddChar.{p2m_u_0, 0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  G (fun x => Complex)
                  (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  chi u)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
              @Ne.{1} Complex
                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                    (@AddChar.{p2m_u_0, 0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                    G (fun x => Complex)
                    (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                    chi v)
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
                @Ne.{1} Complex
                  (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi
                    (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                      (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d)
                        v)))
                  (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst chi
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
                      u)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_third_probe_separates_exceptional

