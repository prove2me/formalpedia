-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualComponent_squarefree_profiles_of_medium
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:15:44.658062+00:00
-- url     : https://prove2.me/submissions/3f9b7d26-efe0-42ac-87f8-e1c42a5a74bc

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

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

theorem exponentialDeviation_le_two_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ)
    (hsmall : ∀ omega, |S omega| ≤ 1) :
    mu.exponentialDeviation S ≤
      2 * mu.expect (fun omega ↦ |S omega|) := by
  unfold exponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    mu.mass omega * |Real.exp (S omega) - 1| ≤
        mu.mass omega * (2 * |S omega|) :=
      mul_le_mul_of_nonneg_left
        (Real.abs_exp_sub_one_le (hsmall omega)) (mu.mass_nonneg omega)
    _ = 2 * (mu.mass omega * |S omega|) := by ring

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

/- Source module: Erdos390.Full.DivisibilityMomentBounds -/
section


/-!
# Exact multiple-counting moment bounds

The omitted-local-score step in Lemma 7.5 expands a valuation score into
divisor indicators and then counts common multiples.  This file proves that
finite combinatorial step for an arbitrary set of positive integers bounded
by one physical endpoint.  No smooth-number estimate or probability-model
assumption enters here.
-/

open scoped BigOperators

namespace Erdos390.Full.DivisibilityMomentBounds

open ArithmeticModel

noncomputable section

/-- A subset of positive integers up to `M` has at most `M / D` members
divisible by a modulus `D`. -/
theorem card_filter_dvd_le_div (S : Finset ℕ) {M D : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (S.filter (D ∣ ·)).card ≤ M / D := by
  have hsubset : S.filter (D ∣ ·) ⊆
      (Finset.Ioc 0 M).filter (D ∣ ·) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_Ioc.mpr ⟨hSpos m hm.1, hSle m hm.1⟩, hm.2⟩
  calc
    (S.filter (D ∣ ·)).card ≤
        ((Finset.Ioc 0 M).filter (D ∣ ·)).card :=
      Finset.card_le_card hsubset
    _ = M / D := Nat.Ioc_filter_dvd_card_eq_div M D

/-- A finite sum of an actual divisor indicator is the cardinality of the
corresponding filtered set. -/
theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]

/-- Products of divisor indicators combine by least common multiple. -/
theorem divInd_mul_eq_lcm (a b m : ℕ) :
    divInd a m * divInd b m = divInd (Nat.lcm a b) m := by
  by_cases ha : a ∣ m
  · by_cases hb : b ∣ m
    · have hlcm : Nat.lcm a b ∣ m := Nat.lcm_dvd ha hb
      simp [divInd, ha, hb, hlcm]
    · have hnlcm : ¬Nat.lcm a b ∣ m := by
        intro h
        exact hb ((Nat.dvd_lcm_right a b).trans h)
      simp [divInd, ha, hb, hnlcm]
  · have hnlcm : ¬Nat.lcm a b ∣ m := by
      intro h
      exact ha ((Nat.dvd_lcm_left a b).trans h)
    simp [divInd, ha, hnlcm]

/-- For coprime moduli, products of divisor indicators use the ordinary
product modulus. -/
theorem divInd_mul_eq_product_of_coprime {a b m : ℕ}
    (hcop : Nat.Coprime a b) :
    divInd a m * divInd b m = divInd (a * b) m := by
  rw [divInd_mul_eq_lcm, hcop.lcm_eq_mul]





private theorem sum_divInd_le_real_div (S : Finset ℕ) {M N : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (∑ m ∈ S, divInd N m) ≤ (M : ℝ) / (N : ℝ) := by
  rw [sum_divInd_eq_card_filter]
  calc
    ((S.filter (N ∣ ·)).card : ℝ) ≤ ((M / N : ℕ) : ℝ) := by
      exact_mod_cast card_filter_dvd_le_div S hSpos hSle
    _ ≤ (M : ℝ) / (N : ℝ) := Nat.cast_div_le

/-- Exact first-moment multiple-counting bound.  The coprimality condition
is precisely the paper's omission of the forced local primes from the
global score. -/
theorem sum_marked_divisorScore_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    (∑ m ∈ S, divInd D m * divisorScore R m) ≤
      ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hterm : ∀ a ∈ R,
      (∑ m ∈ S, divInd (D * a) m) ≤
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
    intro a ha
    calc
      (∑ m ∈ S, divInd (D * a) m) ≤
          (M : ℝ) / ((D * a : ℕ) : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
        have hD0 : (D : ℝ) ≠ 0 := by positivity
        have ha0 : (a : ℝ) ≠ 0 := by
          exact_mod_cast (hRpos a ha).ne'
        norm_num only [Nat.cast_mul]
        field_simp [hD0, ha0]
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) =
        ∑ a ∈ R, ∑ m ∈ S, divInd (D * a) m := by
      unfold divisorScore
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro m hm
      exact divInd_mul_eq_product_of_coprime (hcop a ha)
    _ ≤ ∑ a ∈ R,
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
      exact Finset.sum_le_sum fun a ha => hterm a ha
    _ = ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]









private theorem endpoint_card_ratio_le {S : Finset ℕ} {M : ℕ} {c : ℝ}
    (hc : 0 < c) (hM : 0 < M)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ)) :
    (M : ℝ) / (S.card : ℝ) ≤ 1 / c := by
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hMle : (M : ℝ) ≤ (S.card : ℝ) / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcard)
  calc
    (M : ℝ) / (S.card : ℝ) ≤
        ((S.card : ℝ) / c) / (S.card : ℝ) :=
      div_le_div_of_nonneg_right hMle hcardPos.le
    _ = 1 / c := by field_simp [ne_of_gt hc, ne_of_gt hcardPos]

/-- Normalized first omitted-score moment.  A lower density bound for the
cell converts the exact endpoint count into the paper's `1/D` scale. -/
theorem uniformAverage_marked_divisorScore_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    uniformAverage S (fun m => divInd D m * divisorScore R m) ≤
      (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hsum := sum_marked_divisorScore_le S R hD hSpos hSle hRpos hcop
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hrecipNonneg : 0 ≤ ∑ a ∈ R, 1 / (a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    positivity
  have hfactor : 0 ≤ (1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) :=
    mul_nonneg (by positivity) hrecipNonneg
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) / (S.card : ℝ) ≤
        (((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) /
          (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) := by ring
    _ ≤ (1 / c) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio hfactor
    _ = (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by ring







end

end Erdos390.Full.DivisibilityMomentBounds

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

/-- If the score itself is pointwise at most one, first marked and unmarked
absolute moments give a completely explicit version of the normalization
bound. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_small_score
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hsmall : ∀ omega, |S omega| ≤ 1)
    (htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let b := mu.expect (fun omega ↦ A omega * |S omega|)
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hb0 : 0 ≤ b := mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA0 omega) (abs_nonneg _)
  have hp0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have hdelta : delta ≤ 2 * a :=
    mu.exponentialDeviation_le_two_expect_abs S hsmall
  have hdelta1 : delta < 1 := hdelta.trans_lt htotal
  have heta : eta ≤ 2 * b := by
    unfold eta markedExponentialDeviation b expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega _
    calc
      mu.mass omega *
          (A omega * |Real.exp (S omega) - 1|) ≤
          mu.mass omega * (A omega * (2 * |S omega|)) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        exact mul_le_mul_of_nonneg_left
          (Real.abs_exp_sub_one_le (hsmall omega)) (hA0 omega)
      _ = 2 * (mu.mass omega * (A omega * |S omega|)) := by ring
  have hbase :=
    mu.abs_exponentialTilt_expect_sub_expect_le A S hA0 hA1 hdelta1
  refine hbase.trans ?_
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hdenA : 0 < 1 - 2 * a := sub_pos.mpr htotal
  apply (div_le_div_iff₀ hdenDelta hdenA).2
  have hnum : eta + mu.expect A * delta ≤
      2 * b + 2 * mu.expect A * a := by
    calc
      eta + mu.expect A * delta ≤
          2 * b + mu.expect A * (2 * a) :=
        add_le_add heta (mul_le_mul_of_nonneg_left hdelta hp0)
      _ = 2 * b + 2 * mu.expect A * a := by ring
  nlinarith



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









end

end Erdos390.Full.OmittedScoreCell

end

/- Source module: Erdos390.Full.ValuationTiltCell -/
section


/-!
# Actual compact valuation tilts on a finite cell

This file substitutes the genuine valuation score into the omitted-score
comparison.  Both divisor-score moments are discharged by exact
common-multiple counting; no probabilistic independence is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.ValuationTiltCell

open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination

noncomputable section





/-- Uniform bound for the genuine compact valuation score using the physical
logarithm rather than the (much larger) number of prime-power columns. -/
theorem abs_valuationScore_le_log_ratio
    (P : Finset ℕ) (eta : ℕ → ℝ) {m M W : ℕ} {B L : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p)
    (hB : 0 ≤ B) (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := by
  unfold valuationScore
  calc
    |∑ p ∈ P, (eta p / L) * valuation p m| ≤
        ∑ p ∈ P, |(eta p / L) * valuation p m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ P, (|eta p| / L) * valuation p m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (valuation_nonneg p m)]
    _ ≤ ∑ p ∈ P, (B / L) * valuation p m := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (valuation_nonneg p m)
    _ = (B / L) * (∑ p ∈ P, valuation p m) := by
      rw [Finset.mul_sum]
    _ ≤ (B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_valuation_le_log_ratio P hm hmM hW hpW)
        (div_nonneg hB hL.le)



end

end Erdos390.Full.ValuationTiltCell

end

/- Source module: Erdos390.Full.TwoLocalRestoration -/
section


/-!
# Exact restoration of two omitted local primes

The omitted-score marked law is reweighted by the two literal local
valuation fugacities.  This file proves the exact finite identity connecting
that sequential reweighting to the full valuation tilt and then expands both
the marked numerator and the normalizer into prime-power indicators.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Two finite probability objects are equal when their mass functions are
equal.  The remaining structure fields are propositions. -/
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h

/-- Exponential tilting first by `S` and then by `T` is exactly tilting once
by their sum. -/
theorem exponentialTilt_add (mu : FiniteProbability Omega)
    (S T : Omega → ℝ) :
    (mu.exponentialTilt S).exponentialTilt T =
      mu.exponentialTilt (fun omega ↦ S omega + T omega) := by
  apply eq_of_mass_eq
  funext omega
  have hpart :
      (mu.exponentialTilt S).expPartition T =
        mu.expPartition (fun x ↦ S x + T x) / mu.expPartition S := by
    unfold expPartition
    rw [mu.exponentialTilt_expect_eq (fun x ↦ Real.exp (T x)) S]
    congr 1
    unfold expect
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only
    rw [Real.exp_add]
    ring
  change
    (mu.mass omega * Real.exp (S omega) / mu.expPartition S) *
          Real.exp (T omega) /
        (mu.exponentialTilt S).expPartition T =
      mu.mass omega * Real.exp (S omega + T omega) /
        mu.expPartition (fun x ↦ S x + T x)
  rw [hpart]
  rw [Real.exp_add]
  field_simp [ne_of_gt (mu.expPartition_pos S),
    ne_of_gt (mu.expPartition_pos (fun x ↦ S x + T x))]



end FiniteProbability

namespace TwoLocalRestoration









section Cell

variable {S : Finset ℕ}





end Cell

end TwoLocalRestoration

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.OmittedTiltFallback -/
section


/-!
# Arbitrary-modulus fallback under an omitted valuation tilt

The four-mark theorem gives the sharp Dickman main term.  Terms outside that
chamber only require an upper bound.  This file proves the required fallback
directly: a bounded exponential tilt changes every nonnegative event by at
most its pointwise density-ratio bound, and elementary multiple counting on
an actual positive cell gives the reciprocal divisor scale for every modulus.
-/

namespace Erdos390.Full

open ArithmeticModel DivisibilityMomentBounds

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- The partition function of a score bounded in absolute value by `K` is at
least `exp (-K)`. -/
theorem exp_neg_le_expPartition (mu : FiniteProbability Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-K) ≤ mu.expPartition score := by
  unfold expPartition expect
  calc
    Real.exp (-K) = ∑ omega, mu.mass omega * Real.exp (-K) := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]
    _ ≤ ∑ omega, mu.mass omega * Real.exp (score omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr ((neg_le_neg (hscore omega)).trans
        (neg_abs_le (score omega)))

/-- Pointwise bounded tilting changes any nonnegative expectation by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_expect_le_exp_two_mul
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    (mu.exponentialTilt score).expect A ≤
      Real.exp (2 * K) * mu.expect A := by
  have hZpos : 0 < mu.expPartition score := mu.expPartition_pos score
  have hZlower : Real.exp (-K) ≤ mu.expPartition score :=
    mu.exp_neg_le_expPartition score K hscore
  have hEA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA
  have hnum0 : 0 ≤ mu.expect (fun omega ↦ A omega * Real.exp (score omega)) :=
    mu.expect_nonneg _ fun omega ↦ mul_nonneg (hA omega) (Real.exp_pos _).le
  have hnum : mu.expect (fun omega ↦ A omega * Real.exp (score omega)) ≤
      Real.exp K * mu.expect A := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    calc
      mu.mass omega * (A omega * Real.exp (score omega)) ≤
          mu.mass omega * (A omega * Real.exp K) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        apply mul_le_mul_of_nonneg_left _ (hA omega)
        exact Real.exp_le_exp.mpr ((le_abs_self (score omega)).trans
          (hscore omega))
      _ = Real.exp K * (mu.mass omega * A omega) := by ring
  have hinv : (mu.expPartition score)⁻¹ ≤ Real.exp K := by
    apply (inv_le_iff_one_le_mul₀ hZpos).2
    calc
      1 = Real.exp K * Real.exp (-K) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp K * mu.expPartition score :=
        mul_le_mul_of_nonneg_left hZlower (Real.exp_pos K).le
  rw [mu.exponentialTilt_expect_eq A score, div_eq_mul_inv]
  calc
    mu.expect (fun omega ↦ A omega * Real.exp (score omega)) *
        (mu.expPartition score)⁻¹ ≤
      (Real.exp K * mu.expect A) * (mu.expPartition score)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hZpos.le)
    _ ≤ (Real.exp K * mu.expect A) * Real.exp K :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (Real.exp_pos K).le hEA0)
    _ = Real.exp (2 * K) * mu.expect A := by
      rw [show Real.exp (2 * K) = Real.exp K * Real.exp K by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

end FiniteProbability

namespace OmittedTiltFallback

open FiniteProbability ValuationScoreDomination ValuationTiltCell

/-- Pure multiple counting: every divisor event on a positive cell of
density at least `c` has probability at most `1/(cD)`. -/
theorem uniformAverage_divInd_le
    (S : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    uniformAverage S (divInd D) ≤ 1 / (c * (D : ℝ)) := by
  have h := uniformAverage_marked_divisorScore_le S {1}
    hD hM hc hcard hSpos hSle
    (fun a ha ↦ by simp at ha; omega)
    (fun a ha ↦ by simp at ha; subst a; simp)
  have hone (m : ℕ) : divisorScore {1} m = 1 := by
    unfold divisorScore
    simp only [Finset.sum_singleton]
    simp [divInd]
  have hleft : (fun m ↦ divInd D m * divisorScore {1} m) = divInd D := by
    funext m
    rw [hone]
    ring
  rw [hleft] at h
  have hsum : (∑ a ∈ ({1} : Finset ℕ), 1 / (a : ℝ)) = 1 := by
    norm_num
  rw [hsum, mul_one] at h
  exact h

/-- Arbitrary-modulus reciprocal fallback for the genuine omitted valuation
tilt on an actual finite cell.  No smoothness or four-mark condition is
assumed on `D`. -/
theorem omittedValuationTilt_divInd_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D W : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hW : 1 < W) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hpW : ∀ p ∈ P, W ≤ p) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) ≤
      Real.exp (2 * ((B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)))) /
          (c * (D : ℝ)) := by
  let mu := uniformOnFinset S hS
  let K : ℝ := (B / L) *
    (Real.log (M : ℝ) / Real.log (W : ℝ))
  have hscore : ∀ m : S, |valuationScore P eta L m| ≤ K := by
    intro m
    simpa only [K] using abs_valuationScore_le_log_ratio P eta
      (hSpos m m.property) (hSle m m.property) hW hpW hB hL heta
  have htilt := mu.exponentialTilt_expect_le_exp_two_mul
    (fun m : S ↦ divInd D m)
    (fun m : S ↦ valuationScore P eta L m) K
    (fun m ↦ divInd_nonneg D m) hscore
  have hbase : mu.expect (fun m : S ↦ divInd D m) ≤
      1 / (c * (D : ℝ)) := by
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    exact uniformAverage_divInd_le S hD hM hc hcard hSpos hSle
  calc
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) ≤ Real.exp (2 * K) *
            mu.expect (fun m : S ↦ divInd D m) := htilt
    _ ≤ Real.exp (2 * K) * (1 / (c * (D : ℝ))) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (2 * ((B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)))) /
          (c * (D : ℝ)) := by
      dsimp only [K, mu]
      ring

end OmittedTiltFallback

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)























theorem scaledBridgeScore_eq_medium_add_nuisance [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.scaledBridgeScore xi m =
      B.scaledMediumScore xi m + B.scaledNuisanceScore xi m := by
  rw [scaledBridgeScore, scaledMediumScore, scaledNuisanceScore,
    B.vectorScore_eq_effectivePrime_add_nuisance xi m]
  rw [add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring





/-- On each tagged cell the global score splits exactly into its medium
valuation part and the remaining physical/head part. -/
theorem sigmaCellScore_scaledBridge_eq [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledBridgeScore xi) c m =
      sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
  exact B.scaledBridgeScore_eq_medium_add_nuisance xi ⟨c, m⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.LocalizedMarkedTiltCovariance -/
section


/-!
# Localized covariance stability under a small exponential tilt

The physical/head residual in the paper is a second, small tilt of each
medium-prime cell law.  A total-variation estimate would lose the divisibility
mark.  This file instead keeps the marginal and joint-event scales visible.

Everything below is an exact statement about finite probability laws.  The
arithmetic application supplies reciprocal bounds for the three marked
events `A`, `B`, and `A * B`.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]





theorem smallTiltLoss_le_eight_mul {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1) :
    smallTiltLoss epsilon ≤ 8 * epsilon := by
  have hden : 0 < 1 - 2 * epsilon := by nlinarith
  unfold smallTiltLoss
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg epsilon]

/-- A pointwise score of size `epsilon` changes a marked probability only
by the same relative scale.  In particular, an event of baseline probability
`O(1 / d)` changes by `O(epsilon / d)`, with no additive TV loss. -/
theorem abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    {epsilon a : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      smallTiltLoss epsilon * a := by
  have hExpectAbs : mu.expect (fun omega ↦ |S omega|) ≤ epsilon := by
    calc
      mu.expect (fun omega ↦ |S omega|) ≤
          mu.expect (fun _ ↦ epsilon) := mu.expect_mono _ _ hscore
      _ = epsilon := by simp [expect, ← Finset.sum_mul, mu.mass_sum]
  have hAexpect0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have ha0 : 0 ≤ a := hAexpect0.trans hAexpect
  have hMarked :
      mu.expect (fun omega ↦ A omega * |S omega|) ≤ epsilon * a := by
    calc
      mu.expect (fun omega ↦ A omega * |S omega|) ≤
          mu.expect (fun omega ↦ A omega * epsilon) := by
        apply mu.expect_mono
        intro omega
        exact mul_le_mul_of_nonneg_left (hscore omega) (hA0 omega)
      _ = epsilon * mu.expect A := by
        rw [show (fun omega ↦ A omega * epsilon) =
            fun omega ↦ epsilon * A omega by
          funext omega
          ring]
        rw [mu.expect_smul]
      _ ≤ epsilon * a := mul_le_mul_of_nonneg_left hAexpect hepsilon
  have htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1 := by
    calc
      2 * mu.expect (fun omega ↦ |S omega|) ≤ 2 * epsilon :=
        mul_le_mul_of_nonneg_left hExpectAbs (by norm_num)
      _ < 1 := hsmall
  have hbase := mu.abs_exponentialTilt_expect_sub_expect_le_of_small_score
    A S hA0 hA1 (fun omega ↦ (hscore omega).trans (by linarith)) htotal
  have hdenActual : 0 < 1 - 2 * mu.expect (fun omega ↦ |S omega|) :=
    sub_pos.mpr htotal
  have hdenEpsilon : 0 < 1 - 2 * epsilon := sub_pos.mpr hsmall
  have hnum :
      2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        4 * epsilon * a := by
    have hsecond : mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        a * epsilon :=
      mul_le_mul hAexpect hExpectAbs
        (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) ha0
    nlinarith
  refine hbase.trans ?_
  calc
    (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) ≤
        (4 * epsilon * a) /
          (1 - 2 * mu.expect (fun omega ↦ |S omega|)) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (4 * epsilon * a) / (1 - 2 * epsilon) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg (by norm_num) hepsilon) ha0
      · exact hdenEpsilon
      · linarith
    _ = smallTiltLoss epsilon * a := by
      unfold smallTiltLoss
      field_simp









end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeNuisanceTiltFallback -/
section


/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- On a literal cell, the medium part of the bridge score is the genuine
valuation score used by the structured-cell estimates. -/
theorem sigmaCellScore_scaledMedium_eq_valuationScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledMediumScore xi) c m =
      valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L m := by
  unfold sigmaCellScore scaledMediumScore valuationScore
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ (B.effectiveNatCoefficient xi p / B.L) * valuation p m)
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.effectiveNatCoefficient_of_mem xi p.2]
  simp only [StructuredSampleData.value]









private theorem sum_nuisanceCoord {I : Type*} [Fintype I]
    (f : NuisanceCoord I → ℝ) :
    (∑ z : NuisanceCoord I, f z) =
      f .physical + ∑ h : I, f (.head h) := by
  calc
    (∑ z : NuisanceCoord I, f z) =
        ∑ s : Unit ⊕ I, f ((nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I).symm s) := by
      exact Fintype.sum_equiv (nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I) f
        (fun s ↦ f ((nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback I).symm s)) (fun z ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback]

/-- The head part is literally constant on each tagged cell. -/
theorem sigmaCellScore_scaledNuisance_eq_physical_add_constant
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledNuisanceScore xi) c m =
      B.cellPhysicalTiltScore xi c m + B.cellHeadTiltConstant xi c := by
  unfold sigmaCellScore scaledNuisanceScore cellPhysicalTiltScore
    cellHeadTiltConstant
  rw [PiLp.inner_apply, sum_nuisanceCoord]
  simp only [B.nuisanceParameter_physical, B.nuisanceStatistic_physical,
    B.nuisanceParameter_head, B.nuisanceStatistic_head]
  unfold centeredHeadScore headIndicator StructuredSampleData.cellOf
  rw [add_div]
  congr 1
  · simp only [RCLike.inner_apply, conj_trivial]
    ring
  · apply congrArg (fun z : ℝ ↦ z / B.L)
    apply Finset.sum_congr rfl
    intro h hh
    split_ifs <;> simp only [RCLike.inner_apply, conj_trivial] <;> ring

private theorem exponentialTilt_const
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (k : ℝ) :
    mu.exponentialTilt (fun _ ↦ k) = mu := by
  apply FiniteProbability.eq_of_mass_eq
  funext omega
  have hpart : mu.expPartition (fun _ ↦ k) = Real.exp k := by
    unfold expPartition expect
    calc
      (∑ x, mu.mass x * Real.exp k) =
          (∑ x, mu.mass x) * Real.exp k := by rw [Finset.sum_mul]
      _ = Real.exp k := by rw [mu.mass_sum, one_mul]
  change mu.mass omega * Real.exp k /
      mu.expPartition (fun _ ↦ k) = mu.mass omega
  rw [hpart]
  field_simp [ne_of_gt (Real.exp_pos k)]

/-- Adding the constant cell-head factor does not change a normalized
exponential tilt. -/
theorem exponentialTilt_cellNuisance_eq_physical [Nonempty Head]
    (c : Cell Head)
    (mu : FiniteProbability (B.sampleData.SampleAt c))
    (xi : B.ParamSpace) :
    mu.exponentialTilt
        (sigmaCellScore (B.scaledNuisanceScore xi) c) =
      mu.exponentialTilt (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledNuisanceScore xi) c =
      fun m ↦ B.cellPhysicalTiltScore xi c m +
        B.cellHeadTiltConstant xi c := by
    funext m
    exact B.sigmaCellScore_scaledNuisance_eq_physical_add_constant xi c m
  rw [hscore, ← mu.exponentialTilt_add]
  rw [exponentialTilt_const]

/-- Exact component-law factorization: full bridge tilt equals medium tilt
followed by the small physical tilt. -/
theorem guardedCell_fullTilt_eq_medium_physicalTilt [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.guardedCellProbability c).exponentialTilt
        (sigmaCellScore (B.scaledBridgeScore xi) c) =
      (B.cellMediumLaw xi c).exponentialTilt
        (B.cellPhysicalTiltScore xi c) := by
  have hscore : sigmaCellScore (B.scaledBridgeScore xi) c =
      fun m ↦ sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
    funext m
    exact B.sigmaCellScore_scaledBridge_eq xi c m
  rw [hscore, ← (B.guardedCellProbability c).exponentialTilt_add]
  exact B.exponentialTilt_cellNuisance_eq_physical
    c (B.cellMediumLaw xi c) xi

/-- The actual guard-deleted cell endpoint is positive. -/
theorem cell_hi_pos (c : Cell Head) :
    0 < B.sampleData.hi c.2 := by
  obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
  let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
  have hmle : m ≤ B.sampleData.hi c.2 := by
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hmpos : 0 < m := by
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  exact hmpos.trans_le hmle

/-- Reciprocal fallback for the literal medium-tilted, guard-deleted cell.
The required density lower bound is stated as the concrete cardinality
inequality that the guard census supplies. -/
theorem cellMediumLaw_expect_divInd_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A : ℝ} {D : ℕ}
    (hD : 0 < D) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) :
    (B.cellMediumLaw xi c).expect
        (fun m ↦ divInd D m) ≤
      Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
        (rho * (D : ℝ)) := by
  let S := B.sampleData.cellFinset c
  have hS : S.Nonempty := B.sampleData.cell_nonempty c
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ A := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hSle : ∀ m ∈ S, m ≤ B.sampleData.hi c.2 := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hraw := omittedValuationTilt_divInd_le
    S (primeBand B.sampleData.n B.sampleData.W) hS
    (B.effectiveNatCoefficient xi)
    hD (B.cell_hi_pos c) hA B.L_pos hW hrho hcard hSpos hSle hpW hetaNat
  have hscore :
      sigmaCellScore (B.scaledMediumScore xi) c =
      fun m : B.sampleData.SampleAt c ↦
        valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ) := by
    funext m
    exact B.sigmaCellScore_scaledMedium_eq_valuationScore xi c m
  change (((uniformOnFinset S hS).exponentialTilt
      (sigmaCellScore (B.scaledMediumScore xi) c)).expect
        (fun m : B.sampleData.SampleAt c ↦ divInd D m)) ≤ _
  rw [hscore]
  exact hraw

/-- A fixed physical interval and a bounded physical parameter make the
second tilt pointwise `O(1/L)`. -/
theorem abs_cellPhysicalTiltScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {Aphys Kphys : ℝ}
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys) :
    ∀ m, |B.cellPhysicalTiltScore xi c m| ≤
      Aphys * Kphys / B.L := by
  intro m
  unfold cellPhysicalTiltScore
  rw [abs_mul, abs_div, abs_of_pos B.L_pos]
  calc
    (|xi MomentCoord.physical| / B.L) *
        |B.physicalScore ⟨c, m⟩| ≤
      (Aphys / B.L) * Kphys := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hAphys B.L_pos.le
        · exact hKphys m
        · exact abs_nonneg _
        · exact div_nonneg (le_trans (abs_nonneg _) hAphys) B.L_pos.le
    _ = Aphys * Kphys / B.L := by ring



/-- The physical/head second tilt changes a divisor probability at its
original reciprocal scale. -/
theorem abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A Aphys Kphys : ℝ} {D : ℕ}
    (hD : 0 < D) (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).expect
          (fun m ↦ divInd D m) -
        (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m)| ≤
      8 * epsilon * (G * (1 / (D : ℝ))) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon] using
      B.abs_cellPhysicalTiltScore_le xi c hAphys hKphys
  have hmedium := B.cellMediumLaw_expect_divInd_le xi c
    hD hA hW hrho hcard heta
  have hmediumG :
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m) ≤
        G * (1 / (D : ℝ)) := by
    dsimp only [G]
    calc
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D m) ≤
          Real.exp (2 * ((A / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) /
            (rho * (D : ℝ)) := hmedium
      _ = (Real.exp (2 * ((A / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) / rho) *
              (1 / (D : ℝ)) := by ring
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  have htwo : 2 * epsilon < 1 := by
    dsimp only [epsilon] at hsmall ⊢
    nlinarith
  have hraw :=
    FiniteProbability.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (B.cellMediumLaw xi c)
      (fun m ↦ divInd D m) (B.cellPhysicalTiltScore xi c)
      (fun m ↦ divInd_nonneg D m) (fun m ↦ divInd_le_one D m)
      hepsilon0 htwo hscore hmediumG
  have hloss : smallTiltLoss epsilon ≤ 8 * epsilon :=
    smallTiltLoss_le_eight_mul hepsilon0 (by
      simpa only [epsilon] using hsmall)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (Real.exp_pos _).le hrho.le
  have hfactor0 : 0 ≤ G * (1 / (D : ℝ)) := by
    exact mul_nonneg hG0 (by positivity)
  exact hraw.trans (mul_le_mul_of_nonneg_right hloss hfactor0)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















/-- Adding the physical/head component tilt to a common signed medium
profile costs at most `4 epsilon G` in the paper's profile normalization.
The factor four is forced by the one-prime normalization
`singleWeight p 1 = 2/p`; it also dominates the two-prime cost. -/
theorem actualComponent_squarefree_profiles_of_medium [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {Emedium rho A Aphys Kphys : ℝ}
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hpair : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Emedium * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Emedium * singleWeight p 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun m ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value m)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        (Emedium + 4 * epsilon * G) * pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun m ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value m)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        (Emedium + 4 * epsilon * G) * singleWeight p 1) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    dsimp only [epsilon]
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (Real.exp_pos _).le hrho.le
  constructor
  · intro p hp q hq
    have hqBand := (Finset.mem_erase.mp hq).2
    have hpPrime := prime_of_mem_primeBand hp
    have hqPrime := prime_of_mem_primeBand hqBand
    have hD : 0 < pairPower p q 1 1 := by
      unfold pairPower
      simpa only [pow_one] using Nat.mul_pos hpPrime.pos hqPrime.pos
    have htilt := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hD hA hW hrho hcard heta hAphys0 hKphys0 hAphys hKphys hsmall
    have htilt' :
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd (pairPower p q 1 1)
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| ≤
          8 * epsilon * (G * (1 / (pairPower p q 1 1 : ℝ))) := by
      simpa only [actualComponentValuationLaw_probability,
        actualComponentValuationLaw_value, epsilon, G] using htilt
    have hphysical :
        8 * epsilon * (G * (1 / (pairPower p q 1 1 : ℝ))) ≤
          (4 * epsilon * G) * pairWeight p q 1 1 := by
      unfold pairPower pairWeight
      norm_num
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqPrime.pos
      field_simp [hp0.ne', hq0.ne']
      nlinarith [hepsilon0, hG0]
    calc
      |(B.actualComponentValuationLaw xi c).probability.expect
            (fun m ↦ divInd (pairPower p q 1 1)
              ((B.actualComponentValuationLaw xi c).value m)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (pairPower p q 1 1)| ≤
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd (pairPower p q 1 1)
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| +
          |(B.cellMediumLaw xi c).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
              (pairPower p q 1 1)| := by
          calc
            _ = |((B.actualComponentValuationLaw xi c).probability.expect
                    (fun m ↦ divInd (pairPower p q 1 1)
                      ((B.actualComponentValuationLaw xi c).value m)) -
                  (B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))) +
                ((B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                    (pairPower p q 1 1))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ (4 * epsilon * G) * pairWeight p q 1 1 +
          Emedium * pairWeight p q 1 1 :=
        add_le_add (htilt'.trans hphysical) (hpair p hp q hq)
      _ = (Emedium + 4 * epsilon * G) * pairWeight p q 1 1 := by ring
  · intro p hp
    have hpPrime := prime_of_mem_primeBand hp
    have htilt := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hpPrime.pos hA hW hrho hcard heta hAphys0 hKphys0
      hAphys hKphys hsmall
    have htilt' :
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd p
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ))| ≤
          8 * epsilon * (G * (1 / (p : ℝ))) := by
      simpa only [actualComponentValuationLaw_probability,
        actualComponentValuationLaw_value, epsilon, G] using htilt
    have hphysical : 8 * epsilon * (G * (1 / (p : ℝ))) =
        (4 * epsilon * G) * singleWeight p 1 := by
      unfold singleWeight
      norm_num
      ring
    calc
      |(B.actualComponentValuationLaw xi c).probability.expect
            (fun m ↦ divInd p
              ((B.actualComponentValuationLaw xi c).value m)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        |(B.actualComponentValuationLaw xi c).probability.expect
              (fun m ↦ divInd p
                ((B.actualComponentValuationLaw xi c).value m)) -
            (B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ))| +
          |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
            PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| := by
          calc
            _ = |((B.actualComponentValuationLaw xi c).probability.expect
                    (fun m ↦ divInd p
                      ((B.actualComponentValuationLaw xi c).value m)) -
                  (B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd p (m : ℕ))) +
                ((B.cellMediumLaw xi c).expect
                    (fun m ↦ divInd p (m : ℕ)) -
                  PaperScaleMarkedCell.paperDivisibilityMain
                    B.sampleData.n p)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ (4 * epsilon * G) * singleWeight p 1 +
          Emedium * singleWeight p 1 :=
        add_le_add (htilt'.trans hphysical.le) (hsingle p hp)
      _ = (Emedium + 4 * epsilon * G) * singleWeight p 1 := by ring



















/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) {Emedium rho A Aphys Kphys : Real},
  LE.le.{0} (0 : Real) A →
    LT.lt.{0} (1 : Nat)
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
      LT.lt.{0} (0 : Real) rho →
        LE.le.{0}
            (HMul.hMul.{0, 0, 0} rho
              ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
            ↑(Finset.card.{0}
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c)) →
          (∀
              (r :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} B xi r))
                A) →
            LE.le.{0} (0 : Real) Aphys →
              LE.le.{0} (0 : Real) Kphys →
                LE.le.{0}
                    (abs.{0}
                      (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}))
                    Aphys →
                  (∀
                      (m :
                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c),
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B (Sigma.mk.{u_1, 0} c m)))
                        Kphys) →
                    LE.le.{0}
                        (HMul.hMul.{0, 0, 0} (8 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys Kphys)
                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                        (1 : Real) →
                      (∀ (p : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              p →
                            ∀ (q : Nat),
                              Membership.mem.{0, 0}
                                  (Finset.erase.{0}
                                    (Erdos390.Full.ArithmeticModel.primeBand
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                    p)
                                  q →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (Erdos390.Full.FiniteProbability.expect.{0}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c)
                                        fun m =>
                                        Erdos390.Full.ArithmeticModel.divInd
                                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                        (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                  (HMul.hMul.{0, 0, 0} Emedium
                                    (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
                        (∀ (p : Nat),
                            Membership.mem.{0, 0}
                                (Erdos390.Full.ArithmeticModel.primeBand
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                p →
                              LE.le.{0}
                                (abs.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (Erdos390.Full.FiniteProbability.expect.{0}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c) fun m =>
                                      Erdos390.Full.ArithmeticModel.divInd p ↑m)
                                    (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                      p)))
                                (HMul.hMul.{0, 0, 0} Emedium
                                  (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                          have epsilon :=
                            HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys Kphys)
                              (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B);
                          have G :=
                            HDiv.hDiv.{0, 0, 0}
                              (Real.exp
                                (HMul.hMul.{0, 0, 0} (2 : Real)
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} A (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (Real.log
                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
                                      (Real.log
                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))))
                              rho;
                          And
                            (∀ (p : Nat),
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                  p →
                                ∀ (q : Nat),
                                  Membership.mem.{0, 0}
                                      (Finset.erase.{0}
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                        p)
                                      q →
                                    LE.le.{0}
                                      (abs.{0}
                                        (HSub.hSub.{0, 0, 0}
                                          (Erdos390.Full.FiniteProbability.expect.{0}
                                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                  u_2}
                                                B xi c))
                                            fun m =>
                                            Erdos390.Full.ArithmeticModel.divInd
                                              (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat))
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                    u_2}
                                                  B xi c)
                                                m))
                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                      (HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0} Emedium
                                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) epsilon) G))
                                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                            (∀ (p : Nat),
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                  p →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (Erdos390.Full.FiniteProbability.expect.{0}
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                              u_2}
                                            B xi c))
                                        fun m =>
                                        Erdos390.Full.ArithmeticModel.divInd p
                                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                u_2}
                                              B xi c)
                                            m))
                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                        p)))
                                  (HMul.hMul.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0} Emedium
                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) epsilon) G))
                                    (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualComponent_squarefree_profiles_of_medium
