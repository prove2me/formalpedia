-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_sign_same_correct
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:48.240211+00:00
-- url     : https://prove2.me/submissions/bf627439-c83a-419e-8497-63206b31dccf

import Aesop
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_prediction_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_ball_iff
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS



theorem recoh_rational_sign_same_iff (base observed : RecohRationalComplex)
    (radius : ℚ) :
    recohRationalSignSame base observed radius = true ↔
      0 ≤ radius ∧ ‖recohRationalComplexValue observed -
        recohRationalComplexValue base‖ ≤ (radius : ℝ) := by
  rw [recohRationalSignSame, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, (recoh_rational_ball_iff observed base radius hr).mp h⟩
  · rintro ⟨hr, h⟩
    exact ⟨hr, (recoh_rational_ball_iff observed base radius hr).mpr h⟩

/-- A true sign is recovered despite errors in both measurement and base
prediction.  The sufficient budget is explicit and asymmetric. -/
theorem p2m_local_recoh_rational_sign_same_correct
    (truth : ℂ) (base observed : RecohRationalComplex) (radius : ℚ)
    (ε η : ℝ) (positive : Bool) (hradius : 0 ≤ radius)
    (hamplitude : 1 ≤ ‖truth‖)
    (hpred : ‖recohRationalComplexValue base - truth‖ ≤ η)
    (hobs : ‖recohRationalComplexValue observed - (if positive then truth else -truth)‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : ε + ((radius : ℝ) + η) < 2) :
    recohRationalSignSame base observed radius = positive := by
  cases positive with
  | true =>
    apply (recoh_rational_sign_same_iff base observed radius).mpr
    refine ⟨hradius, le_trans ?_ hcomplete⟩
    exact recoh_noisy_prediction_sound _ _ _ η ε
      (by simpa only [norm_sub_rev] using hpred) (by simpa using hobs)
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hsame
    have hfit := ((recoh_rational_sign_same_iff base observed radius).mp hsame).2
    have hplus := recoh_noisy_prediction_sound _ _ _ η (radius : ℝ) hpred hfit
    have hminus : ‖recohRationalComplexValue observed - -truth‖ ≤ ε := by simpa using hobs
    have htriangle : ‖truth - -truth‖ ≤ (radius : ℝ) + η + ε := by
      calc
        ‖truth - -truth‖ = ‖(truth - recohRationalComplexValue observed) +
            (recohRationalComplexValue observed - -truth)‖ := by congr 1; ring
        _ ≤ ‖truth - recohRationalComplexValue observed‖ +
            ‖recohRationalComplexValue observed - -truth‖ := norm_add_le _ _
        _ ≤ (radius : ℝ) + η + ε :=
          add_le_add (by simpa only [norm_sub_rev] using hplus) hminus
    rw [recoh_opposite_probe_distance] at htriangle
    linarith

variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2





















end Couret.STROBO2TORS


theorem solution : ∀ (truth : Complex) (base observed : Couret.STROBO2TORS.RecohRationalComplex) (radius : Rat) (ε η : Real)
  (positive : Bool),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) radius →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@Norm.norm.{0} Complex Complex.instNorm truth) →
      @LE.le.{0} Real Real.instLE
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
              (Couret.STROBO2TORS.recohRationalComplexValue base) truth))
          η →
        @LE.le.{0} Real Real.instLE
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                (Couret.STROBO2TORS.recohRationalComplexValue observed)
                (@ite.{1} Complex (@Eq.{1} Bool positive Bool.true) (instDecidableEqBool positive Bool.true) truth
                  (@Neg.neg.{0} Complex Complex.instNeg truth))))
            ε →
          @LE.le.{0} Real Real.instLE (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ε η)
              (@Rat.cast.{0} Real Real.instRatCast radius) →
            @LT.lt.{0} Real Real.instLT
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ε
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Rat.cast.{0} Real Real.instRatCast radius) η))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
              @Eq.{1} Bool (Couret.STROBO2TORS.recohRationalSignSame base observed radius) positive := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_sign_same_correct

