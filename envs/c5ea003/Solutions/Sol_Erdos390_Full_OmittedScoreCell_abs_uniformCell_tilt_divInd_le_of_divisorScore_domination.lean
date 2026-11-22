-- Prove2me | solution 1 for Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:50:53.068137+00:00
-- url     : https://prove2.me/submissions/328cbbc6-7ed4-4689-842a-30abb9194379

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.Full.FiniteTiltTV -/
section


/-!
# Total-variation control for finite exponential tilts

This supplies the normalization estimate used to compare each finite-`n`
tilted nuisance covariance with its own finite-`n` baseline.  The bound is
proved directly from the exponential density ratio.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]











theorem exponentialDeviation_nonneg (mu : FiniteProbability Omega)
    (S : Omega → ℝ) : 0 ≤ mu.exponentialDeviation S := by
  unfold exponentialDeviation expect
  exact Finset.sum_nonneg fun omega _ ↦
    mul_nonneg (mu.mass_nonneg omega) (abs_nonneg _)



theorem abs_expPartition_sub_one_le_deviation
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    |mu.expPartition S - 1| ≤ mu.exponentialDeviation S := by
  have hrewrite : mu.expPartition S - 1 =
      ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
    calc
      mu.expPartition S - 1 =
          (∑ omega, mu.mass omega * Real.exp (S omega)) -
            ∑ omega, mu.mass omega := by
              rw [expPartition, expect, mu.mass_sum]
      _ = ∑ omega,
          (mu.mass omega * Real.exp (S omega) - mu.mass omega) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
  rw [hrewrite]
  calc
    |∑ omega, mu.mass omega * (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.exponentialDeviation S := by
      unfold exponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]

theorem expPartition_lower_bound
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    1 - mu.exponentialDeviation S ≤ mu.expPartition S := by
  have h := mu.abs_expPartition_sub_one_le_deviation S
  have hneg : -mu.exponentialDeviation S ≤
      -|mu.expPartition S - 1| := neg_le_neg h
  have habs : -|mu.expPartition S - 1| ≤
      mu.expPartition S - 1 := neg_abs_le _
  linarith





end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel















































theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

theorem divInd_le_one (d m : ℕ) : divInd d m ≤ 1 := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]





















































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]









theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)





















end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedScoreTilt -/
section


/-!
# Normalized marked-event bounds under an omitted-score tilt

The four-mark step in Lemma 7.5 first omits the forced local primes from
the score, estimates a marked numerator, and then divides by the tilted
partition function.  This file proves that normalization step for an actual
finite probability law.  The result keeps the marked and unmarked
exponential deviations separate, so a `1 / D` marked moment is not replaced
by an unscaled total-variation error.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]



theorem markedExponentialDeviation_nonneg
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    0 ≤ mu.markedExponentialDeviation A S := by
  unfold markedExponentialDeviation
  exact mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA omega) (abs_nonneg _)

/-- Global real-exponential increment bound, with no smallness hypothesis. -/
theorem abs_exp_sub_one_le_exp_abs_mul_abs (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| * |x| := by
  by_cases hx : 0 ≤ x
  · have hexpOne : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hbase := Real.add_one_le_exp (-x)
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos x).le
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hprod] at hmul
    rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr hexpOne)]
    nlinarith [Real.exp_pos x]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hexpOne : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hxneg.le
    have hlinear := Real.add_one_le_exp x
    have hone : 1 ≤ Real.exp (-x) := Real.one_le_exp (neg_nonneg.mpr hxneg.le)
    have hmul : -x ≤ Real.exp (-x) * (-x) := by
      simpa using
        (mul_le_mul_of_nonneg_right hone (neg_nonneg.mpr hxneg.le))
    rw [abs_of_neg hxneg, abs_of_nonpos (sub_nonpos.mpr hexpOne)]
    nlinarith

/-- A pointwise score bound converts the marked first absolute moment into
an exponential-deviation bound.  The constant may depend on the already
fixed score box, while the arithmetic mark remains visible. -/
theorem markedExponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) {K : ℝ}
    (hA : ∀ omega, 0 ≤ A omega)
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.markedExponentialDeviation A S ≤
      Real.exp K * mu.expect (fun omega ↦ A omega * |S omega|) := by
  unfold markedExponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  have hexp : Real.exp |S omega| ≤ Real.exp K :=
    Real.exp_le_exp.mpr (hbound omega)
  have hinc : |Real.exp (S omega) - 1| ≤
      Real.exp K * |S omega| := by
    exact (abs_exp_sub_one_le_exp_abs_mul_abs (S omega)).trans
      (mul_le_mul_of_nonneg_right hexp (abs_nonneg _))
  calc
    mu.mass omega * (A omega * |Real.exp (S omega) - 1|) ≤
        mu.mass omega * (A omega * (Real.exp K * |S omega|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinc (hA omega))
        (mu.mass_nonneg omega)
    _ = Real.exp K * (mu.mass omega * (A omega * |S omega|)) := by ring

theorem exponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ) {K : ℝ}
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.exponentialDeviation S ≤
      Real.exp K * mu.expect (fun omega ↦ |S omega|) := by
  have hmarked := mu.markedExponentialDeviation_le_exp_mul_expect_abs
    (fun _ ↦ (1 : ℝ)) S (fun _ ↦ zero_le_one) hbound
  simpa [markedExponentialDeviation] using hmarked





/-- The marked numerator differs from its untilted value by at most the
marked exponential deviation. -/
theorem abs_expWeighted_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    |mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
        mu.expect A| ≤ mu.markedExponentialDeviation A S := by
  have hrearrange :
      mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
          mu.expect A =
        ∑ omega, mu.mass omega * A omega *
          (Real.exp (S omega) - 1) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  rw [hrearrange]
  calc
    |∑ omega, mu.mass omega * A omega *
        (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * A omega *
          (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.markedExponentialDeviation A S := by
      unfold markedExponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_mul, abs_of_nonneg (mu.mass_nonneg omega),
        abs_of_nonneg (hA omega)]
      ring

/-- Exact normalization inequality for a marked event/statistic.  Unlike a
global total-variation estimate, the leading numerator error retains the
mark and hence its arithmetic `1 / D` scale. -/
theorem abs_exponentialTilt_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hdev : mu.exponentialDeviation S < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (mu.markedExponentialDeviation A S +
          mu.expect A * mu.exponentialDeviation S) /
        (1 - mu.exponentialDeviation S) := by
  let Z := mu.expPartition S
  let p := mu.expect A
  let N := mu.expect (fun omega ↦ A omega * Real.exp (S omega))
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hdenpos : 0 < 1 - delta := sub_pos.mpr hdev
  have hZlower : 1 - delta ≤ Z := mu.expPartition_lower_bound S
  have hp0 : 0 ≤ p := mu.expect_nonneg A hA0
  have hp1 : p ≤ 1 := by
    calc
      p ≤ mu.expect (fun _ ↦ (1 : ℝ)) := mu.expect_mono A _ hA1
      _ = 1 := by simp [expect, mu.mass_sum]
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have heta0 : 0 ≤ eta :=
    mu.markedExponentialDeviation_nonneg A S hA0
  have hN : |N - p| ≤ eta := by
    exact mu.abs_expWeighted_expect_sub_expect_le A S hA0
  have hZ : |Z - 1| ≤ delta :=
    mu.abs_expPartition_sub_one_le_deviation S
  rw [mu.exponentialTilt_expect_eq A S]
  change |N / Z - p| ≤ (eta + p * delta) / (1 - delta)
  have hid : N / Z - p = ((N - p) + p * (1 - Z)) / Z := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hZpos]
  have hnum : |(N - p) + p * (1 - Z)| ≤ eta + p * delta := by
    calc
      |(N - p) + p * (1 - Z)| ≤
          |N - p| + |p * (1 - Z)| := abs_add_le _ _
      _ = |N - p| + p * |Z - 1| := by
        rw [abs_mul, abs_of_nonneg hp0, abs_sub_comm 1 Z]
      _ ≤ eta + p * delta := by
        exact add_le_add hN (mul_le_mul_of_nonneg_left hZ hp0)
  calc
    |(N - p) + p * (1 - Z)| / Z ≤
        (eta + p * delta) / Z :=
      div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (eta + p * delta) / (1 - delta) := by
      apply div_le_div_of_nonneg_left
      · exact add_nonneg heta0 (mul_nonneg hp0 hdelta0)
      · exact hdenpos
      · exact hZlower



/-- Box-uniform version of the same result.  Only the explicit factor
`exp K` depends on the pointwise score box; the marked first moment is left
on its original arithmetic scale. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_bounded_score
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) {K : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hbound : ∀ omega, |S omega| ≤ K)
    (htotal : Real.exp K * mu.expect (fun omega ↦ |S omega|) < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (Real.exp K * mu.expect (fun omega ↦ A omega * |S omega|) +
          Real.exp K * mu.expect A *
            mu.expect (fun omega ↦ |S omega|)) /
        (1 - Real.exp K * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let b := mu.expect (fun omega ↦ A omega * |S omega|)
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hb0 : 0 ≤ b := mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA0 omega) (abs_nonneg _)
  have hp0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have hdelta : delta ≤ Real.exp K * a :=
    mu.exponentialDeviation_le_exp_mul_expect_abs S hbound
  have hdelta1 : delta < 1 := hdelta.trans_lt htotal
  have heta : eta ≤ Real.exp K * b :=
    mu.markedExponentialDeviation_le_exp_mul_expect_abs A S hA0 hbound
  have hbase :=
    mu.abs_exponentialTilt_expect_sub_expect_le A S hA0 hA1 hdelta1
  refine hbase.trans ?_
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hdenA : 0 < 1 - Real.exp K * a := sub_pos.mpr htotal
  have hnum : eta + mu.expect A * delta ≤
      Real.exp K * b + Real.exp K * mu.expect A * a := by
    calc
      eta + mu.expect A * delta ≤
          Real.exp K * b + mu.expect A * (Real.exp K * a) :=
        add_le_add heta (mul_le_mul_of_nonneg_left hdelta hp0)
      _ = Real.exp K * b + Real.exp K * mu.expect A * a := by ring
  have htarget0 : 0 ≤ Real.exp K * b + Real.exp K * mu.expect A * a := by
    exact add_nonneg
      (mul_nonneg (Real.exp_pos K).le hb0)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0) ha0)
  calc
    (eta + mu.expect A * delta) / (1 - delta) ≤
        (Real.exp K * b + Real.exp K * mu.expect A * a) /
          (1 - delta) :=
      div_le_div_of_nonneg_right hnum hdenDelta.le
    _ ≤ (Real.exp K * b + Real.exp K * mu.expect A * a) /
          (1 - Real.exp K * a) := by
      apply div_le_div_of_nonneg_left htarget0 hdenA
      linarith

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.UniformFiniteProbability -/
section


/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}





/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedScoreCell -/
section


/-!
# Omitted-score normalization on an actual arithmetic cell

This module composes the genuine uniform probability law of a finite cell
with the marked exponential-tilt inequality.  All expectations in the result
are literal counting averages over that same cell; there is no implicit
identification between a counting formula and an abstract probability law.
-/

namespace Erdos390.Full.OmittedScoreCell

open FiniteProbability DivisibilityMomentBounds

noncomputable section

/-- Counting average on a nonempty finite cell is exactly expectation under
its genuine uniform finite probability law. -/
theorem uniform_expect_eq_uniformAverage
    (S : Finset ℕ) (hS : S.Nonempty) (F : ℕ → ℝ) :
    (uniformOnFinset S hS).expect (fun m : S ↦ F m) =
      uniformAverage S F := by
  rw [uniformOnFinset_expect_ambient_eq]
  rfl

/-- Exact marked-event comparison after a bounded score tilt, written only
in terms of actual cell averages. -/
theorem abs_uniformCell_tilt_expect_sub_average_le
    (S : Finset ℕ) (hS : S.Nonempty) (A score : ℕ → ℝ) {K : ℝ}
    (hA0 : ∀ m ∈ S, 0 ≤ A m)
    (hA1 : ∀ m ∈ S, A m ≤ 1)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K *
        uniformAverage S (fun m ↦ |score m|) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect (fun m : S ↦ A m) -
        uniformAverage S A| ≤
      (Real.exp K * uniformAverage S
          (fun m ↦ A m * |score m|) +
        Real.exp K * uniformAverage S A *
          uniformAverage S (fun m ↦ |score m|)) /
        (1 - Real.exp K *
          uniformAverage S (fun m ↦ |score m|)) := by
  have havgA :
      (uniformOnFinset S hS).expect (fun m : S ↦ A m) =
        uniformAverage S A :=
    uniform_expect_eq_uniformAverage S hS A
  have havgAbs :
      (uniformOnFinset S hS).expect (fun m : S ↦ |score m|) =
        uniformAverage S (fun m ↦ |score m|) :=
    uniform_expect_eq_uniformAverage S hS (fun m ↦ |score m|)
  have havgMarked :
      (uniformOnFinset S hS).expect
          (fun m : S ↦ A m * |score m|) =
        uniformAverage S (fun m ↦ A m * |score m|) :=
    uniform_expect_eq_uniformAverage S hS
      (fun m ↦ A m * |score m|)
  have hbase :=
    (uniformOnFinset S hS).abs_exponentialTilt_expect_sub_expect_le_of_bounded_score
      (fun m : S ↦ A m) (fun m : S ↦ score m)
      (fun m ↦ hA0 m m.property)
      (fun m ↦ hA1 m m.property)
      (fun m ↦ hscore m m.property)
      (by rw [havgAbs]; exact htotal)
  rw [havgA, havgAbs, havgMarked] at hbase
  exact hbase

/-- Divisibility indicators satisfy the exact event hypotheses in the
preceding theorem. -/
theorem abs_uniformCell_tilt_divInd_sub_average_le
    (S : Finset ℕ) (hS : S.Nonempty) (D : ℕ) (score : ℕ → ℝ) {K : ℝ}
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K *
        uniformAverage S (fun m ↦ |score m|) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * |score m|) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          uniformAverage S (fun m ↦ |score m|)) /
        (1 - Real.exp K *
          uniformAverage S (fun m ↦ |score m|)) := by
  apply abs_uniformCell_tilt_expect_sub_average_le S hS
  · intro m hm
    exact ArithmeticModel.divInd_nonneg D m
  · intro m hm
    exact ArithmeticModel.divInd_le_one D m
  · exact hscore
  · exact htotal

/-- The paper-facing form: a weighted omitted score is pointwise dominated
by `beta` times the divisor-indicator score.  The conclusion now depends only
on the first unmarked and marked divisor-score moments, exactly the quantities
supplied by `DivisibilityMomentBounds`. -/
theorem abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
    (S R : Finset ℕ) (hS : S.Nonempty) (D : ℕ)
    (score : ℕ → ℝ) {K beta : ℝ}
    (hdom : ∀ m ∈ S,
      |score m| ≤ beta * divisorScore R m)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K * beta *
        uniformAverage S (divisorScore R) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * uniformAverage S (divisorScore R))) /
        (1 - Real.exp K * beta *
          uniformAverage S (divisorScore R)) := by
  let mu := uniformOnFinset S hS
  let p := uniformAverage S (ArithmeticModel.divInd D)
  let a := uniformAverage S (fun m ↦ |score m|)
  let Abar := beta * uniformAverage S (divisorScore R)
  let b := uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * |score m|)
  let Bbar := beta * uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)
  have ha : a ≤ Abar := by
    have hmono := mu.expect_mono
      (fun m : S ↦ |score m|)
      (fun m : S ↦ beta * divisorScore R m)
      (fun m ↦ hdom m m.property)
    rw [uniform_expect_eq_uniformAverage S hS
        (fun m ↦ |score m|),
      uniform_expect_eq_uniformAverage S hS
        (fun m ↦ beta * divisorScore R m)] at hmono
    have hfactor : uniformAverage S
        (fun m ↦ beta * divisorScore R m) =
        beta * uniformAverage S (divisorScore R) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring
    simpa only [a, Abar, hfactor] using hmono
  have hb : b ≤ Bbar := by
    have hpoint (m : S) :
        ArithmeticModel.divInd D m * |score m| ≤
          beta * (ArithmeticModel.divInd D m * divisorScore R m) := by
      have hmark := ArithmeticModel.divInd_nonneg D m
      calc
        ArithmeticModel.divInd D m * |score m| ≤
            ArithmeticModel.divInd D m *
              (beta * divisorScore R m) :=
          mul_le_mul_of_nonneg_left (hdom m m.property) hmark
        _ = beta *
            (ArithmeticModel.divInd D m * divisorScore R m) := by ring
    have hmono := mu.expect_mono
      (fun m : S ↦ ArithmeticModel.divInd D m * |score m|)
      (fun m : S ↦ beta *
        (ArithmeticModel.divInd D m * divisorScore R m)) hpoint
    rw [uniform_expect_eq_uniformAverage S hS
        (fun m ↦ ArithmeticModel.divInd D m * |score m|),
      uniform_expect_eq_uniformAverage S hS
        (fun m ↦ beta *
          (ArithmeticModel.divInd D m * divisorScore R m))] at hmono
    have hfactor : uniformAverage S
        (fun m ↦ beta *
          (ArithmeticModel.divInd D m * divisorScore R m)) =
        beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring
    simpa only [b, Bbar, hfactor] using hmono
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    rw [← uniform_expect_eq_uniformAverage S hS
      (ArithmeticModel.divInd D)]
    exact mu.expect_nonneg _ fun m ↦ ArithmeticModel.divInd_nonneg D m
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    rw [← uniform_expect_eq_uniformAverage S hS (fun m ↦ |score m|)]
    exact mu.expect_nonneg _ fun m ↦ abs_nonneg _
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    rw [← uniform_expect_eq_uniformAverage S hS
      (fun m ↦ ArithmeticModel.divInd D m * |score m|)]
    exact mu.expect_nonneg _ fun m ↦
      mul_nonneg (ArithmeticModel.divInd_nonneg D m) (abs_nonneg _)
  have hAbar0 : 0 ≤ Abar := ha0.trans ha
  have hBbar0 : 0 ≤ Bbar := hb0.trans hb
  have hactualTotal : Real.exp K * a < 1 := by
    calc
      Real.exp K * a ≤ Real.exp K * Abar :=
        mul_le_mul_of_nonneg_left ha (Real.exp_pos K).le
      _ < 1 := by simpa only [Abar, mul_assoc] using htotal
  have hraw := abs_uniformCell_tilt_divInd_sub_average_le
    S hS D score hscore (by simpa only [a] using hactualTotal)
  change |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤ _
  have hraw' :
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤
        (Real.exp K * b + Real.exp K * p * a) /
          (1 - Real.exp K * a) := by
    simpa only [p, a, b] using hraw
  refine hraw'.trans ?_
  have hdenActual : 0 < 1 - Real.exp K * a :=
    sub_pos.mpr hactualTotal
  have hdenBound : 0 < 1 - Real.exp K * Abar := by
    simpa only [Abar, mul_assoc] using sub_pos.mpr htotal
  have hnum :
      Real.exp K * b + Real.exp K * p * a ≤
        Real.exp K * Bbar + Real.exp K * p * Abar := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hb (Real.exp_pos K).le)
      (mul_le_mul_of_nonneg_left ha
        (mul_nonneg (Real.exp_pos K).le hp0))
  have htarget0 :
      0 ≤ Real.exp K * Bbar + Real.exp K * p * Abar :=
    add_nonneg
      (mul_nonneg (Real.exp_pos K).le hBbar0)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0) hAbar0)
  calc
    (Real.exp K * b + Real.exp K * p * a) /
        (1 - Real.exp K * a) ≤
      (Real.exp K * Bbar + Real.exp K * p * Abar) /
        (1 - Real.exp K * a) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (Real.exp K * Bbar + Real.exp K * p * Abar) /
        (1 - Real.exp K * Abar) := by
      apply div_le_div_of_nonneg_left htarget0 hdenBound
      linarith [mul_le_mul_of_nonneg_left ha (Real.exp_pos K).le]
    _ = (Real.exp K * beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * uniformAverage S (divisorScore R))) /
        (1 - Real.exp K * beta *
          uniformAverage S (divisorScore R)) := by
      dsimp only [Abar, Bbar, p]
      ring



end

end Erdos390.Full.OmittedScoreCell

end

theorem solution :
∀ (S R : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (D : Nat) (score : Nat → Real) {K beta : Real},
  (∀ (m : Nat),
      Membership.mem.{0, 0} S m →
        LE.le.{0} (abs.{0} (score m))
          (HMul.hMul.{0, 0, 0} beta (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m))) →
    (∀ (m : Nat), Membership.mem.{0, 0} S m → LE.le.{0} (abs.{0} (score m)) K) →
      LT.lt.{0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
            (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
              (Erdos390.Full.DivisibilityMomentBounds.divisorScore R)))
          (1 : Real) →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (Erdos390.Full.FiniteProbability.expect.{0}
                (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                  (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun m => score ↑m)
                fun m => Erdos390.Full.ArithmeticModel.divInd D ↑m)
              (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S (Erdos390.Full.ArithmeticModel.divInd D))))
          (HDiv.hDiv.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S fun m =>
                  HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticModel.divInd D m)
                    (Erdos390.Full.DivisibilityMomentBounds.divisorScore R m)))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (Real.exp K)
                  (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S (Erdos390.Full.ArithmeticModel.divInd D)))
                (HMul.hMul.{0, 0, 0} beta
                  (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                    (Erdos390.Full.DivisibilityMomentBounds.divisorScore R)))))
            (HSub.hSub.{0, 0, 0} (1 : Real)
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp K) beta)
                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S
                  (Erdos390.Full.DivisibilityMomentBounds.divisorScore R))))) := by
  exact @Erdos390.Full.OmittedScoreCell.abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
