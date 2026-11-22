-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T13:34:22.449986+00:00
-- url     : https://prove2.me/submissions/33b9aa8a-1b1a-4a7f-a037-95991d92fe61

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

set_option autoImplicit false

universe u_1 u_2

-- ===== from Full/ArithmeticModel.lean =====
open scoped BigOperators
namespace Erdos390.Full.ArithmeticModel
theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

theorem divInd_le_one (d m : ℕ) : divInd d m ≤ 1 := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

theorem valuation_eq_sum_divInd_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuation p m = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  have hMpow : m ≤ p ^ M := by
    exact hmM.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  have hfilter := Nat.Ico_filter_pow_dvd_eq hp hm.ne' hMpow
  have hcard := Nat.factorization_eq_card_pow_dvd m hp
  calc
    valuation p m = (m.factorization p : ℝ) := rfl
    _ = (((Finset.Ico 1 m).filter fun k => p ^ k ∣ m).card : ℝ) := by
      exact_mod_cast hcard
    _ = (((Finset.Icc 1 M).filter fun k => p ^ k ∣ m).card : ℝ) := by
      rw [hfilter]
    _ = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
      simp [positiveExponents, divInd]

private theorem positiveExponents_eq_insert_high {M : ℕ} (hM : 1 ≤ M) :
    positiveExponents M = insert 1 (highExponents M) := by
  ext k
  simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
  omega

theorem higherValuation_eq_sum_high_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m = ∑ k ∈ highExponents M, divInd (p ^ k) m := by
  have hM : 1 ≤ M := hm.trans_le hmM
  rw [higherValuation, valuation_eq_sum_divInd_of_le hp hm hmM,
    positiveExponents_eq_insert_high hM]
  have h1not : 1 ∉ highExponents M := by simp
  rw [Finset.sum_insert h1not]
  simp [divInd]

theorem higherValuation_eq_sum_high {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ∑ k ∈ highExponents m, divInd (p ^ k) m :=
  higherValuation_eq_sum_high_of_le hp hm le_rfl

theorem higherValuation_nonneg {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    0 ≤ higherValuation p m := by
  rw [higherValuation_eq_sum_high hp hm]
  exact Finset.sum_nonneg fun k hk => divInd_nonneg (p ^ k) m

end Erdos390.Full.ArithmeticModel

-- ===== from Full/DivisibilityMomentBounds.lean =====
open scoped BigOperators
namespace Erdos390.Full.DivisibilityMomentBounds
open ArithmeticModel
noncomputable section
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

theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]

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

-- ===== from Full/PrimePowerCovariance.lean =====
open scoped BigOperators
namespace Erdos390.Full
noncomputable section
namespace FiniteProbability
variable {Omega Iota : Type*} [Fintype Omega]
theorem expect_zero (mu : FiniteProbability Omega) :
    mu.expect (fun _ ↦ 0) = 0 := by
  simp [expect]

theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)

theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring

theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

end FiniteProbability
namespace PrimePowerCovariance
open ArithmeticModel
namespace BoundedValuationLaw
variable {Omega : Type*} [Fintype Omega] {M : ℕ}
theorem V_eq_I_add_J (law : BoundedValuationLaw Omega M) (p : ℕ) :
    law.V p = fun omega ↦ law.I p omega + law.J p omega := by
  funext omega
  simp only [V, I, J, higherValuation]
  ring

theorem covVV_sub_covII (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    law.covVV p q - law.covII p q =
      law.covJI p q + law.covIJ p q + law.covJJ p q := by
  rw [covVV, covII, covJI, covIJ, covJJ,
    law.V_eq_I_add_J p, law.V_eq_I_add_J q]
  rw [law.probability.covariance_add_left,
    law.probability.covariance_add_right,
    law.probability.covariance_add_right]
  ring

theorem I_nonneg (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    0 ≤ law.I p omega := divInd_nonneg _ _

theorem J_nonneg (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    0 ≤ law.J p omega := higherValuation_nonneg hp (law.value_pos omega)

end BoundedValuationLaw
end PrimePowerCovariance
end
end Erdos390.Full

-- ===== from Full/FiniteTiltTV.lean =====
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

-- ===== from Full/OmittedScoreTilt.lean =====
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

-- ===== from Full/UniformFiniteProbability.lean =====
open scoped BigOperators
namespace Erdos390.Full
noncomputable section
namespace FiniteProbability
variable {Alpha : Type*}
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

theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability
end
end Erdos390.Full

-- ===== from Full/OmittedScoreCell.lean =====
namespace Erdos390.Full.OmittedScoreCell
open FiniteProbability DivisibilityMomentBounds
noncomputable section
theorem uniform_expect_eq_uniformAverage
    (S : Finset ℕ) (hS : S.Nonempty) (F : ℕ → ℝ) :
    (uniformOnFinset S hS).expect (fun m : S ↦ F m) =
      uniformAverage S F := by
  rw [uniformOnFinset_expect_ambient_eq]
  rfl

end
end Erdos390.Full.OmittedScoreCell

-- ===== from Full/ValuationTiltCell.lean =====
open scoped BigOperators
namespace Erdos390.Full.ValuationTiltCell
open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination
noncomputable section
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

-- ===== from Full/PrimeSums.lean =====
open scoped BigOperators Nat.Prime
open Filter Topology
namespace Erdos390.Full.PrimeSums
open ArithmeticModel Scale
private theorem inv_sq_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega)]
    norm_num
  have hrhs :
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) =
        1 / ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
    field_simp [hk0.ne', hk10.ne']
    nlinarith [hcast]
  rw [hrhs]
  gcongr
  nlinarith

private theorem telescope_Icc_le_inv (W Y : ℕ) (hW : 1 ≤ W) :
    (∑ k ∈ Finset.Icc (W + 1) Y,
      (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) ≤ 1 / (W : ℝ) := by
  by_cases hWY : W ≤ Y
  · have hset : Finset.Icc (W + 1) Y = Finset.Ico (W + 1) (Y + 1) := by
      ext k
      simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range ((Y + 1) - (W + 1)),
        1 / ((((W + 1) + i) - 1 : ℕ) : ℝ) - 1 / ((W + 1 + i : ℕ) : ℝ) =
          1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ) := by
      intro i hi
      congr 2 <;> norm_cast <;> omega
    rw [Finset.sum_congr rfl hterm]
    have htel := Finset.sum_range_sub' (fun i : ℕ => 1 / ((W + i : ℕ) : ℝ)) (Y - W)
    rw [show (Y + 1) - (W + 1) = Y - W by omega]
    have htel' :
        (∑ i ∈ Finset.range (Y - W),
          (1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ))) =
            1 / ((W + 0 : ℕ) : ℝ) - 1 / ((W + (Y - W) : ℕ) : ℝ) := by
      simpa only [Nat.add_assoc] using htel
    rw [htel']
    exact sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (W + 1) Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hempty]
    simp

theorem bandReciprocalSquareSum_le (n W : ℕ) (hW : 1 ≤ W) :
    bandReciprocalSquareSum n W ≤ 1 / (W : ℝ) := by
  calc
    bandReciprocalSquareSum n W ≤
        ∑ p ∈ primeBand n W,
          (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_sq_le_telescope (by
        have := cutoff_lt_of_mem_primeBand hp
        omega)
    _ ≤ ∑ k ∈ Finset.Icc (W + 1) (yNat n),
          (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := mem_primeBand.mp hp
        simp [h.2.1, h.2.2]
      · intro k hk hnot
        have hk' := Finset.mem_Icc.mp hk
        have hk2 : 2 ≤ k := by omega
        exact le_trans (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)
          (inv_sq_le_telescope hk2)
    _ ≤ 1 / (W : ℝ) := telescope_Icc_le_inv W (yNat n) hW

end Erdos390.Full.PrimeSums

-- ===== from Full/LocalFugacityBounds.lean =====
open scoped BigOperators
namespace Erdos390.Full.LocalFugacityBounds
open LocalFugacity
noncomputable section
private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb

theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two

theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring

private theorem summable_quadraticHalfTerm : Summable quadraticHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hsq : Summable
      (fun i : ℕ ↦ (i : ℝ) ^ 2 * (1 / (2 : ℝ)) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable (fun i : ℕ ↦ (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two
  convert ((hsq.mul_left 2).add (hlin.mul_left 7)).add
    (hconst.mul_left 3) using 1
  funext i
  unfold quadraticHalfTerm
  push_cast
  ring

theorem sum_shifted_quadratic_half_le_mass (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
          (1 / (2 : ℝ)) ^ (r - 2)) ≤ quadraticHalfMass := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, quadraticHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hweight : 2 * r - 3 = 2 * (r - 2) + 1 := by omega
      have hshift : r + 1 = (r - 2) + 3 := by omega
      unfold quadraticHalfTerm g
      rw [hweight]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show (r : ℝ) + 1 = ((r - 2 : ℕ) : ℝ) + 3 by
        exact_mod_cast hshift]
    · exact hinj
  rw [heq, quadraticHalfMass]
  exact summable_quadraticHalfTerm.sum_le_tsum (s.image g)
    (fun i hi ↦ by unfold quadraticHalfTerm; positivity)

theorem sum_diagonalWeight_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hweight0 : (0 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      have hnum0 : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2))) ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
              (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * quadraticHalfMass :=
      mul_le_mul_of_nonneg_left (sum_shifted_quadratic_half_le_mass R)
        (by positivity)
    _ = quadraticHalfMass / (p : ℝ) ^ 2 := by ring

end
end Erdos390.Full.LocalFugacityBounds

-- ===== from Full/ValuationCutoff.lean =====
namespace Erdos390.Full.ValuationCutoff
open ArithmeticModel LocalFugacityRestoration
noncomputable section
theorem factorization_le_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    m.factorization p ≤ valuationCutoff p M := by
  have hdvd : p ^ m.factorization p ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').2 le_rfl
  have hpowm : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm hdvd
  exact Nat.le_log_of_pow_le hp.one_lt (hpowm.trans hmM)

end
end Erdos390.Full.ValuationCutoff

-- ===== from Full/TwoLocalRestoration.lean =====
open scoped BigOperators
namespace Erdos390.Full
open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff
noncomputable section
namespace FiniteProbability
variable {Omega : Type*} [Fintype Omega]
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h

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

-- ===== from Full/OmittedTiltFallback.lean =====
namespace Erdos390.Full
open ArithmeticModel DivisibilityMomentBounds
noncomputable section
namespace FiniteProbability
variable {Omega : Type*} [Fintype Omega]
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

-- ===== from Full/FiniteProbabilityMixturePerturbation.lean =====
open scoped BigOperators
namespace Erdos390.Full.FiniteProbability
noncomputable section
variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]
theorem abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ d) :
    |(sigmaMixture weight nu).expect (fun x ↦ Fnu x.1 x.2) -
        (sigmaMixture weight mu).expect (fun x ↦ Fmu x.1 x.2)| ≤ d := by
  rw [sigmaMixture_expect, sigmaMixture_expect]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ c, (weight.mass c * (nu c).expect (Fnu c) -
        weight.mass c * (mu c).expect (Fmu c))| ≤
        ∑ c, |weight.mass c * (nu c).expect (Fnu c) -
          weight.mass c * (mu c).expect (Fmu c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, weight.mass c *
        |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

theorem sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {d : ℝ}
    (hcell : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ d) :
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤ d := by
  have hpoint (i : I) :
      |(sigmaMixture weight nu).expect (fun x ↦ Hnu x.1 i x.2) -
          (sigmaMixture weight mu).expect (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
    rw [sigmaMixture_expect, sigmaMixture_expect,
      ← Finset.sum_sub_distrib]
    calc
      |∑ c, (weight.mass c * (nu c).expect (Hnu c i) -
          weight.mass c * (mu c).expect (Hmu c i))| ≤
          ∑ c, |weight.mass c * (nu c).expect (Hnu c i) -
            weight.mass c * (mu c).expect (Hmu c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← mul_sub, abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight nu).expect
          (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).expect
          (fun x ↦ Hmu x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c *
          |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i,
        |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * d := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = d := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

theorem sum_abs_sigmaMixture_expect_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (H : ∀ c, I → Omega c → ℝ)
    {A : ℝ}
    (hcell : ∀ c, ∑ i, |(mu c).expect (H c i)| ≤ A) :
    ∑ i, |(sigmaMixture weight mu).expect
      (fun x ↦ H x.1 i x.2)| ≤ A := by
  have hpoint (i : I) :
      |(sigmaMixture weight mu).expect (fun x ↦ H x.1 i x.2)| ≤
        ∑ c, weight.mass c * |(mu c).expect (H c i)| := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (H c i)| ≤
          ∑ c, |weight.mass c * (mu c).expect (H c i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
  calc
    ∑ i, |(sigmaMixture weight mu).expect
        (fun x ↦ H x.1 i x.2)| ≤
        ∑ i, ∑ c, weight.mass c * |(mu c).expect (H c i)| :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = ∑ c, weight.mass c * ∑ i, |(mu c).expect (H c i)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ ≤ ∑ c, weight.mass c * A := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = A := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

theorem sum_abs_sigmaMixture_covariance_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dFH : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hFHdiff : ∀ c, ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤ dFH) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dFH + (AF + dF) * dH + AH * dF := by
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let FMu : Sigma Omega → ℝ := fun x ↦ Fmu x.1 x.2
  let FNu : Sigma Theta → ℝ := fun x ↦ Fnu x.1 x.2
  let HMU : I → Sigma Omega → ℝ := fun i x ↦ Hmu x.1 i x.2
  let HNU : I → Sigma Theta → ℝ := fun i x ↦ Hnu x.1 i x.2
  have hFbaseGlobal : |Mu.expect FMu| ≤ AF := by
    rw [sigmaMixture_expect]
    calc
      |∑ c, weight.mass c * (mu c).expect (Fmu c)| ≤
          ∑ c, weight.mass c * |(mu c).expect (Fmu c)| := by
        calc
          _ ≤ ∑ c, |weight.mass c * (mu c).expect (Fmu c)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
      _ ≤ ∑ c, weight.mass c * AF := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_left (hFbase c) (weight.mass_nonneg c)
      _ = AF := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]
  have hHbaseGlobal : ∑ i, |Mu.expect (HMU i)| ≤ AH := by
    simpa only [Mu, HMU] using
      sum_abs_sigmaMixture_expect_le weight mu Hmu hHbase
  have hFdiffGlobal : |Nu.expect FNu - Mu.expect FMu| ≤ dF := by
    simpa only [Nu, Mu, FNu, FMu] using
      abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Fmu Fnu hFdiff
  have hHdiffGlobal : ∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)| ≤ dH := by
    simpa only [Nu, Mu, HNU, HMU] using
      sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
        weight mu nu Hmu Hnu hHdiff
  have hFHdiffGlobal : ∑ i,
      |Nu.expect (fun x ↦ FNu x * HNU i x) -
        Mu.expect (fun x ↦ FMu x * HMU i x)| ≤ dFH := by
    let PHmu : ∀ c, I → Omega c → ℝ :=
      fun c i x ↦ Fmu c x * Hmu c i x
    let PHnu : ∀ c, I → Theta c → ℝ :=
      fun c i x ↦ Fnu c x * Hnu c i x
    have hraw := sum_abs_sigmaMixture_expect_sub_sigmaMixture_expect_le
      weight mu nu PHmu PHnu hFHdiff
    simpa only [Nu, Mu, FNu, FMu, HNU, HMU, PHmu, PHnu] using hraw
  have hFnu : |Nu.expect FNu| ≤ AF + dF := by
    calc
      |Nu.expect FNu| = |(Nu.expect FNu - Mu.expect FMu) + Mu.expect FMu| := by
        congr 1
        ring
      _ ≤ |Nu.expect FNu - Mu.expect FMu| + |Mu.expect FMu| :=
        abs_add_le _ _
      _ ≤ dF + AF := add_le_add hFdiffGlobal hFbaseGlobal
      _ = AF + dF := add_comm _ _
  have hpoint (i : I) :
      |Nu.covariance FNu (HNU i) - Mu.covariance FMu (HMU i)| ≤
        |Nu.expect (fun x ↦ FNu x * HNU i x) -
            Mu.expect (fun x ↦ FMu x * HMU i x)| +
          |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
          |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu| := by
    unfold covariance
    have hprod :
        Nu.expect FNu * Nu.expect (HNU i) -
            Mu.expect FMu * Mu.expect (HMU i) =
          Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i)) +
            Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu) := by ring
    rw [show
      (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Nu.expect FNu * Nu.expect (HNU i)) -
        (Mu.expect (fun x ↦ FMu x * HMU i x) -
          Mu.expect FMu * Mu.expect (HMU i)) =
        (Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)) -
        (Nu.expect FNu * Nu.expect (HNU i) -
          Mu.expect FMu * Mu.expect (HMU i)) by ring,
      hprod]
    let X := Nu.expect (fun x ↦ FNu x * HNU i x) -
      Mu.expect (fun x ↦ FMu x * HMU i x)
    let Y := Nu.expect FNu * (Nu.expect (HNU i) - Mu.expect (HMU i))
    let Z := Mu.expect (HMU i) * (Nu.expect FNu - Mu.expect FMu)
    change |X - (Y + Z)| ≤ _
    calc
      |X - (Y + Z)| ≤ |X| + |Y + Z| := abs_sub _ _
      _ ≤ |X| + (|Y| + |Z|) :=
        add_le_add (le_refl |X|) (abs_add_le Y Z)
      _ = _ := by
        dsimp only [X, Y, Z]
        simp only [abs_mul]
        ring
  calc
    ∑ i, |Nu.covariance FNu (HNU i) -
        Mu.covariance FMu (HMU i)| ≤
      ∑ i, (|Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)| +
        |Nu.expect FNu| * |Nu.expect (HNU i) - Mu.expect (HMU i)| +
        |Mu.expect (HMU i)| * |Nu.expect FNu - Mu.expect FMu|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.expect (fun x ↦ FNu x * HNU i x) -
          Mu.expect (fun x ↦ FMu x * HMU i x)|) +
        |Nu.expect FNu| *
          (∑ i, |Nu.expect (HNU i) - Mu.expect (HMU i)|) +
        (∑ i, |Mu.expect (HMU i)|) *
          |Nu.expect FNu - Mu.expect FMu| := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_mul]
    _ ≤ dFH + (AF + dF) * dH + AH * dF := by
      exact add_le_add
        (add_le_add hFHdiffGlobal
          (mul_le_mul hFnu hHdiffGlobal (by positivity)
            (add_nonneg hAF hdF)))
        (mul_le_mul hHbaseGlobal hFdiffGlobal (by positivity) hAH)

theorem sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (Fmu : ∀ c, Omega c → ℝ) (Fnu : ∀ c, Theta c → ℝ)
    (Hmu : ∀ c, I → Omega c → ℝ)
    (Hnu : ∀ c, I → Theta c → ℝ)
    {AF AH dF dH dCov : ℝ}
    (hAF : 0 ≤ AF) (hAH : 0 ≤ AH)
    (hdF : 0 ≤ dF)
    (hFbase : ∀ c, |(mu c).expect (Fmu c)| ≤ AF)
    (hHbase : ∀ c, ∑ i, |(mu c).expect (Hmu c i)| ≤ AH)
    (hFdiff : ∀ c,
      |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| ≤ dF)
    (hHdiff : ∀ c, ∑ i,
      |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| ≤ dH)
    (hCovdiff : ∀ c, ∑ i,
      |(nu c).covariance (Fnu c) (Hnu c i) -
        (mu c).covariance (Fmu c) (Hmu c i)| ≤ dCov) :
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      dCov + 2 * ((AF + dF) * dH + AH * dF) := by
  have hFnu (c : Cell) : |(nu c).expect (Fnu c)| ≤ AF + dF := by
    calc
      |(nu c).expect (Fnu c)| =
          |((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) +
            (mu c).expect (Fmu c)| := by
        congr 1
        ring
      _ ≤ |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| +
          |(mu c).expect (Fmu c)| := abs_add_le _ _
      _ ≤ dF + AF := add_le_add (hFdiff c) (hFbase c)
      _ = AF + dF := add_comm _ _
  have hprodPoint (c : Cell) (i : I) :
      |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        |(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
    rw [show
      (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i) =
        (nu c).expect (Fnu c) *
            ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)) +
          (mu c).expect (Hmu c i) *
            ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)) by ring]
    simpa only [abs_mul] using abs_add_le
      ((nu c).expect (Fnu c) *
        ((nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)))
      ((mu c).expect (Hmu c i) *
        ((nu c).expect (Fnu c) - (mu c).expect (Fmu c)))
  have hprod (c : Cell) :
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        (AF + dF) * dH + AH * dF := by
    calc
      ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
          (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| ≤
        ∑ i, (|(nu c).expect (Fnu c)| *
            |(nu c).expect (Hnu c i) - (mu c).expect (Hmu c i)| +
          |(mu c).expect (Hmu c i)| *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)|) :=
        Finset.sum_le_sum fun i hi ↦ hprodPoint c i
      _ = |(nu c).expect (Fnu c)| *
            (∑ i, |(nu c).expect (Hnu c i) -
              (mu c).expect (Hmu c i)|) +
          (∑ i, |(mu c).expect (Hmu c i)|) *
            |(nu c).expect (Fnu c) - (mu c).expect (Fmu c)| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ (AF + dF) * dH + AH * dF := by
        exact add_le_add
          (mul_le_mul (hFnu c) (hHdiff c) (by positivity)
            (add_nonneg hAF hdF))
          (mul_le_mul (hHbase c) (hFdiff c) (by positivity) hAH)
  have hFHdiff (c : Cell) : ∑ i,
      |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
        (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
      dCov + ((AF + dF) * dH + AH * dF) := by
    have hpoint (i : I) :
        |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
          |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
      unfold covariance
      rw [show
        (nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
            (mu c).expect (fun x ↦ Fmu c x * Hmu c i x) =
          ((nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
              (nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            ((mu c).expect (fun x ↦ Fmu c x * Hmu c i x) -
              (mu c).expect (Fmu c) * (mu c).expect (Hmu c i))) +
          ((nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)) by ring]
      exact abs_add_le _ _
    calc
      ∑ i, |(nu c).expect (fun x ↦ Fnu c x * Hnu c i x) -
          (mu c).expect (fun x ↦ Fmu c x * Hmu c i x)| ≤
        ∑ i, (|(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)| +
          |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)|) :=
        Finset.sum_le_sum fun i hi ↦ hpoint i
      _ = (∑ i, |(nu c).covariance (Fnu c) (Hnu c i) -
            (mu c).covariance (Fmu c) (Hmu c i)|) +
          ∑ i, |(nu c).expect (Fnu c) * (nu c).expect (Hnu c i) -
            (mu c).expect (Fmu c) * (mu c).expect (Hmu c i)| := by
        rw [Finset.sum_add_distrib]
      _ ≤ dCov + ((AF + dF) * dH + AH * dF) :=
        add_le_add (hCovdiff c) (hprod c)
  have hmain := sum_abs_sigmaMixture_covariance_sub_le
    weight mu nu Fmu Fnu Hmu Hnu hAF hAH hdF
      hFbase hHbase hFdiff hHdiff hFHdiff
  calc
    ∑ i, |(sigmaMixture weight nu).covariance
          (fun x ↦ Fnu x.1 x.2) (fun x ↦ Hnu x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ Fmu x.1 x.2) (fun x ↦ Hmu x.1 i x.2)| ≤
      (dCov + ((AF + dF) * dH + AH * dF)) +
        (AF + dF) * dH + AH * dF := hmain
    _ = dCov + 2 * ((AF + dF) * dH + AH * dF) := by ring

end
end Erdos390.Full.FiniteProbability

-- ===== from Full/FiniteProbabilityMixtureTilt.lean =====
open scoped BigOperators
namespace Erdos390.Full
namespace FiniteProbability
noncomputable section
variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x

end
end FiniteProbability
end Erdos390.Full

-- ===== from Full/FiniteProbabilityPowerCorrectionMixturePerturbation.lean =====
open scoped BigOperators
namespace Erdos390.Full.FiniteProbability
noncomputable section
variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]
theorem sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (IpMu JpMu : ∀ c, Omega c → ℝ)
    (IpNu JpNu : ∀ c, Theta c → ℝ)
    (IqMu JqMu : ∀ c, I → Omega c → ℝ)
    (IqNu JqNu : ∀ c, I → Theta c → ℝ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c, |(mu c).expect (IpMu c)| ≤ AIp)
    (hJpBase : ∀ c, |(mu c).expect (JpMu c)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i, |(mu c).expect (IqMu c i)| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i, |(mu c).expect (JqMu c i)| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(nu c).expect (IpNu c) - (mu c).expect (IpMu c)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(nu c).expect (JpNu c) - (mu c).expect (JpMu c)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(nu c).expect (IqNu c i) - (mu c).expect (IqMu c i)| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(nu c).expect (JqNu c i) - (mu c).expect (JqMu c i)| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (IqNu c i) -
        (mu c).covariance (JpMu c) (IqMu c i)| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (IpNu c) (JqNu c i) -
        (mu c).covariance (IpMu c) (JqMu c i)| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (JqNu c i) -
        (mu c).covariance (JpMu c) (JqMu c i)| ≤ dJJ) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
    let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
    let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
    let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
    let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
    let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
    let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
    let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
  let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
  let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
  let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
  let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
  let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
  let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
  let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
  have hJI := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu IqMu IqNu hAJp hAIrow hdJp
    hJpBase hIqBase hJpDiff hIqDiff hJICovDiff
  have hIJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu IpMu IpNu JqMu JqNu hAIp hAJrow hdIp
    hIpBase hJqBase hIpDiff hJqDiff hIJCovDiff
  have hJJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu JqMu JqNu hAJp hAJrow hdJp
    hJpBase hJqBase hJpDiff hJqDiff hJJCovDiff
  have hpoint (i : I) :
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        |Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)| +
        |Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)| +
        |Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)| := by
    let x := Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)
    let y := Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)
    let z := Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)
    have heq :
        (Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)) = x + y + z := by
      dsimp only [x, y, z]
      ring
    rw [heq]
    exact (abs_add_le (x + y) z).trans
      (add_le_add (abs_add_le x y) (le_refl _))
  calc
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        ∑ i, (|Nu.covariance JpN (IqN i) -
              Mu.covariance JpM (IqM i)| +
            |Nu.covariance IpN (JqN i) -
              Mu.covariance IpM (JqM i)| +
            |Nu.covariance JpN (JqN i) -
              Mu.covariance JpM (JqM i)|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.covariance JpN (IqN i) -
            Mu.covariance JpM (IqM i)|) +
        (∑ i, |Nu.covariance IpN (JqN i) -
            Mu.covariance IpM (JqM i)|) +
        (∑ i, |Nu.covariance JpN (JqN i) -
            Mu.covariance JpM (JqM i)|) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add hJI hIJ) hJJ

open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
theorem sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
    {M : ℕ}
    (weight : FiniteProbability Cell)
    (lawMu : ∀ c, BoundedValuationLaw (Omega c) M)
    (lawNu : ∀ c, BoundedValuationLaw (Theta c) M)
    (p : ℕ) (q : I → ℕ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).I p)| ≤ AIp)
    (hJpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).J p)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).I (q i))| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).J (q i))| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).I p) -
        (lawMu c).probability.expect ((lawMu c).I p)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).J p) -
        (lawMu c).probability.expect ((lawMu c).J p)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).I (q i)) -
        (lawMu c).probability.expect ((lawMu c).I (q i))| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).J (q i)) -
        (lawMu c).probability.expect ((lawMu c).J (q i))| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).I (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).I (q i))| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).I p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).I p) ((lawMu c).J (q i))| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).J (q i))| ≤ dJJ) :
    let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
    let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
    ∑ i, |(Nu.covVV p (q i) - Nu.covII p (q i)) -
        (Mu.covVV p (q i) - Mu.covII p (q i))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
  let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
  have hraw := sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    weight (fun c ↦ (lawMu c).probability)
      (fun c ↦ (lawNu c).probability)
      (fun c ↦ (lawMu c).I p) (fun c ↦ (lawMu c).J p)
      (fun c ↦ (lawNu c).I p) (fun c ↦ (lawNu c).J p)
      (fun c i ↦ (lawMu c).I (q i))
      (fun c i ↦ (lawMu c).J (q i))
      (fun c i ↦ (lawNu c).I (q i))
      (fun c i ↦ (lawNu c).J (q i))
      hAIp hAJp hAIrow hAJrow hdIp hdJp
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJICovDiff hIJCovDiff hJJCovDiff
  have hNu (i : I) :
      Nu.covVV p (q i) - Nu.covII p (q i) =
        Nu.covJI p (q i) + Nu.covIJ p (q i) + Nu.covJJ p (q i) :=
    Nu.covVV_sub_covII p (q i)
  have hMu (i : I) :
      Mu.covVV p (q i) - Mu.covII p (q i) =
        Mu.covJI p (q i) + Mu.covIJ p (q i) + Mu.covJJ p (q i) :=
    Mu.covVV_sub_covII p (q i)
  simpa only [Mu, Nu, hNu, hMu] using hraw

end
end Erdos390.Full.FiniteProbability

-- ===== from Full/LocalizedMarkedTiltCovariance.lean =====
namespace Erdos390.Full
noncomputable section
namespace FiniteProbability
variable {Omega : Type*} [Fintype Omega]
theorem smallTiltLoss_nonneg {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 2 * epsilon < 1) :
    0 ≤ smallTiltLoss epsilon := by
  exact div_nonneg (mul_nonneg (by norm_num) hepsilon)
    (sub_nonneg.mpr hsmall.le)

theorem smallTiltLoss_le_eight_mul {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1) :
    smallTiltLoss epsilon ≤ 8 * epsilon := by
  have hden : 0 < 1 - 2 * epsilon := by nlinarith
  unfold smallTiltLoss
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg epsilon]

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

theorem abs_covariance_sub_covariance_le_of_expectation_perturbations
    (mu nu : FiniteProbability Omega) (A B : Omega → ℝ)
    {a b dA dB dAB : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (ha : mu.expect A ≤ a)
    (hb : mu.expect B ≤ b)
    (hdA0 : 0 ≤ dA)
    (hAperturb : |nu.expect A - mu.expect A| ≤ dA)
    (hBperturb : |nu.expect B - mu.expect B| ≤ dB)
    (hABperturb :
      |nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)| ≤ dAB) :
    |nu.covariance A B - mu.covariance A B| ≤
      dAB + (a + dA) * dB + b * dA := by
  have hmuA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hmuB0 : 0 ≤ mu.expect B := mu.expect_nonneg B hB0
  have ha0 : 0 ≤ a := hmuA0.trans ha
  have hb0 : 0 ≤ b := hmuB0.trans hb
  have hnuA : nu.expect A ≤ a + dA := by
    have hle : nu.expect A - mu.expect A ≤ dA :=
      (le_abs_self _).trans hAperturb
    linarith
  have hnuA0 : 0 ≤ nu.expect A := nu.expect_nonneg A hA0
  have hproduct :
      |nu.expect A * nu.expect B - mu.expect A * mu.expect B| ≤
        (a + dA) * dB + b * dA := by
    rw [show nu.expect A * nu.expect B - mu.expect A * mu.expect B =
        nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A) by ring]
    calc
      |nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A)| ≤
          |nu.expect A * (nu.expect B - mu.expect B)| +
            |mu.expect B * (nu.expect A - mu.expect A)| := abs_add_le _ _
      _ = nu.expect A * |nu.expect B - mu.expect B| +
            mu.expect B * |nu.expect A - mu.expect A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnuA0, abs_of_nonneg hmuB0]
      _ ≤ (a + dA) * dB + b * dA :=
        add_le_add
          (mul_le_mul hnuA hBperturb (abs_nonneg _) (add_nonneg ha0 hdA0))
          (mul_le_mul hb hAperturb (abs_nonneg _) hb0)
  unfold covariance
  rw [show
      (nu.expect (fun omega ↦ A omega * B omega) -
            nu.expect A * nu.expect B) -
          (mu.expect (fun omega ↦ A omega * B omega) -
            mu.expect A * mu.expect B) =
        (nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B) by ring]
  have habs :
      |(nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| :=
    abs_sub _ _
  calc
    |(nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)) -
        (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| := habs
    _ ≤ dAB + ((a + dA) * dB + b * dA) :=
      add_le_add hABperturb hproduct
    _ = dAB + (a + dA) * dB + b * dA := by ring

theorem abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      let D := smallTiltLoss epsilon
      D * c + (a + D * a) * (D * b) + b * (D * a) := by
  dsimp only
  have hD0 : 0 ≤ smallTiltLoss epsilon :=
    smallTiltLoss_nonneg hepsilon hsmall
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hAB1 : ∀ omega, A omega * B omega ≤ 1 := by
    intro omega
    exact (mul_le_mul (hA1 omega) (hB1 omega) (hB0 omega) zero_le_one).trans_eq
      (mul_one 1)
  exact abs_covariance_sub_covariance_le_of_expectation_perturbations
    mu (mu.exponentialTilt S) A B hA0 hB0 hAexpect hBexpect
    (mul_nonneg hD0 ((mu.expect_nonneg A hA0).trans hAexpect))
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      A S hA0 hA1 hepsilon hsmall hscore hAexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      B S hB0 hB1 hepsilon hsmall hscore hBexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (fun omega ↦ A omega * B omega) S hAB0 hAB1 hepsilon hsmall hscore
      hABexpect)

theorem abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * epsilon ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      8 * epsilon * (c + 3 * a * b) := by
  have htwo : 2 * epsilon < 1 := by nlinarith
  have hraw :=
    mu.abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
      A B S hA0 hA1 hB0 hB1 hepsilon htwo hscore
      hAexpect hBexpect hABexpect
  let D := smallTiltLoss epsilon
  have hD0 : 0 ≤ D := smallTiltLoss_nonneg hepsilon htwo
  have hD8 : D ≤ 8 * epsilon := smallTiltLoss_le_eight_mul hepsilon hsmall
  have hD1 : D ≤ 1 := hD8.trans hsmall
  have ha0 : 0 ≤ a := (mu.expect_nonneg A hA0).trans hAexpect
  have hb0 : 0 ≤ b := (mu.expect_nonneg B hB0).trans hBexpect
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hc0 : 0 ≤ c := (mu.expect_nonneg _ hAB0).trans hABexpect
  have hcoef : 2 * D + D ^ 2 ≤ 3 * D := by
    nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hD1)]
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hsum0 : 0 ≤ c + 3 * a * b := by positivity
  refine hraw.trans ?_
  dsimp only
  change
    D * c + (a + D * a) * (D * b) + b * (D * a) ≤
      8 * epsilon * (c + 3 * a * b)
  calc
    D * c + (a + D * a) * (D * b) + b * (D * a) =
        D * c + (2 * D + D ^ 2) * (a * b) := by ring
    _ ≤ D * c + (3 * D) * (a * b) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoef hab0)
    _ = D * (c + 3 * a * b) := by ring
    _ ≤ (8 * epsilon) * (c + 3 * a * b) :=
      mul_le_mul_of_nonneg_right hD8 hsum0

end FiniteProbability
end
end Erdos390.Full

-- ===== from Full/PrimePowerCutoffCovariance.lean =====
open scoped BigOperators
namespace Erdos390.Full.PrimePowerCutoffCovariance
open ArithmeticModel PowerLedger ValuationCutoff
open FiniteProbability PrimePowerCovariance
noncomputable section
private theorem sum_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A, divInd (p ^ k) m) =
      ∑ k ∈ highExponents B, divInd (p ^ k) m := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

theorem higherValuation_eq_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m =
      ∑ k ∈ highExponents (valuationCutoff p M), divInd (p ^ k) m := by
  rw [higherValuation_eq_sum_high_of_le hp hm hmM]
  exact sum_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

namespace FiniteProbability
variable {Omega Iota : Type*} [Fintype Omega]
end FiniteProbability
variable {Omega : Type*} [Fintype Omega] {M : ℕ}
theorem J_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.J p = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M), law.Ip p k omega := by
  funext omega
  exact higherValuation_eq_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

theorem covJI_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) (q : ℕ) :
    law.covJI p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p k) (law.I q) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJI,
    J_eq_valuationCutoff_sum law hp,
    law.probability.covariance_sum_left]

theorem covJJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    law.covJJ p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p k) (law.Ip q l) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJJ,
    J_eq_valuationCutoff_sum law hp,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.covariance_sum_right]

end
end Erdos390.Full.PrimePowerCutoffCovariance

-- ===== from Full/PaperBridgeCellTiltDecomposition.lean =====
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

theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _

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

-- ===== from Full/PaperBridgeNuisanceTiltFallback.lean =====
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

-- ===== from Full/PaperActualSquarefreeReference.lean =====
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
private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁
  cases law₂
  dsimp only at hprob hvalue
  subst_vars
  rfl

theorem sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
    sigmaMixture weight (B.actualComponentValuationLaw xi) =
      B.actualValuationLaw xi := by
  dsimp only
  apply boundedValuationLaw_ext
  · exact congrArg id (B.tiltedLaw_eq_tiltedSigmaMixture xi).symm
  · rfl

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

-- ===== from Full/PaperBridgePhysicalDivisorCovariance.lean =====
namespace Erdos390.Full.PaperBridgeFit
noncomputable section
open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open DivisibilityMomentBounds
namespace BridgeData
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)
theorem abs_guardedCell_fullTilt_divIndCovariance_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A Aphys Kphys : ℝ} {D E : ℕ}
    (hD : 0 < D) (hE : 0 < E)
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
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ divInd D m) (fun m ↦ divInd E m) -
        (B.cellMediumLaw xi c).covariance
          (fun m ↦ divInd D m) (fun m ↦ divInd E m)| ≤
      8 * epsilon *
        (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
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
  have hLcm : 0 < Nat.lcm D E := Nat.lcm_pos hD hE
  have hmediumD := B.cellMediumLaw_expect_divInd_le xi c
    hD hA hW hrho hcard heta
  have hmediumE := B.cellMediumLaw_expect_divInd_le xi c
    hE hA hW hrho hcard heta
  have hmediumLcm := B.cellMediumLaw_expect_divInd_le xi c
    hLcm hA hW hrho hcard heta
  have hDexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd D m) ≤ G * (1 / (D : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (D : ℝ)) := hmediumD
      _ = _ := by ring
  have hEexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd E m) ≤ G * (1 / (E : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (E : ℝ)) := hmediumE
      _ = _ := by ring
  have hproduct : (fun m : B.sampleData.SampleAt c ↦
      divInd D m * divInd E m) =
      fun m : B.sampleData.SampleAt c ↦ divInd (Nat.lcm D E) m := by
    funext m
    exact divInd_mul_eq_lcm D E m
  have hDEexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd D m * divInd E m) ≤
        G * (1 / (Nat.lcm D E : ℝ)) := by
    rw [hproduct]
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (Nat.lcm D E : ℝ)) := hmediumLcm
      _ = _ := by ring
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  exact FiniteProbability.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
    (B.cellMediumLaw xi c)
    (fun m ↦ divInd D m) (fun m ↦ divInd E m)
    (B.cellPhysicalTiltScore xi c)
    (fun m ↦ divInd_nonneg D m) (fun m ↦ divInd_le_one D m)
    (fun m ↦ divInd_nonneg E m) (fun m ↦ divInd_le_one E m)
    hepsilon0 hsmall hscore hDexpect hEexpect hDEexpect

end BridgeData
end
end Erdos390.Full.PaperBridgeFit

-- ===== from Full/PrimePowerLcmGeometry.lean =====
open scoped BigOperators
namespace Erdos390.Full.PrimePowerLcmGeometry
open ArithmeticModel LocalFugacityBounds
noncomputable section
theorem lcm_pow_pow_eq_pow_max (p k l : ℕ) :
    Nat.lcm (p ^ k) (p ^ l) = p ^ max k l := by
  rcases le_total k l with hkl | hlk
  · rw [max_eq_right hkl, Nat.lcm_eq_right_iff_dvd]
    exact pow_dvd_pow p hkl
  · rw [max_eq_left hlk, Nat.lcm_eq_left_iff_dvd]
    exact pow_dvd_pow p hlk

theorem sum_highExponents_pair_inv_lcm_eq_diagonalWeight
    (p A : ℕ) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
  induction A with
  | zero => simp [highExponents]
  | succ A ih =>
      cases A with
      | zero => norm_num [highExponents]
      | succ A =>
          let T := Finset.Icc 2 (Nat.succ A)
          let R := Nat.succ (Nat.succ A)
          have hT : highExponents (Nat.succ A) = T := rfl
          have hR : highExponents R = insert R T := by
            apply Finset.ext
            intro x
            simp only [highExponents, T, R, Finset.mem_Icc,
              Finset.mem_insert]
            omega
          have hRT : R ∉ T := by
            dsimp only [R, T]
            simp
          have hkle (k : ℕ) (hk : k ∈ T) : k ≤ R := by
            have hk' := (Finset.mem_Icc.mp hk).2
            dsimp only [R]
            omega
          have hlcmLeft (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ R) (p ^ k) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_left (hkle k hk)]
          have hlcmRight (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ k) (p ^ R) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_right (hkle k hk)]
          have hcard : T.card = A := by
            dsimp only [T]
            simp
          change
            (∑ k ∈ highExponents R, ∑ l ∈ highExponents R,
                1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
              ∑ r ∈ highExponents R,
                ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r
          rw [hR]
          simp only [Finset.sum_insert hRT]
          rw [show
            (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                (T.card : ℝ) * (1 / (p : ℝ) ^ R) by
              calc
                (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                    ∑ _l ∈ T, 1 / (p : ℝ) ^ R := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  rw [hlcmLeft l hl]
                  norm_num only [Nat.cast_pow]
                _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          rw [show
            (∑ k ∈ T,
                (1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ) +
                  ∑ l ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))) =
              (T.card : ℝ) * (1 / (p : ℝ) ^ R) +
                ∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ k ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ)) =
                  ∑ _k ∈ T, 1 / (p : ℝ) ^ R := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hlcmRight k hk]
                norm_num only [Nat.cast_pow]
              _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          have ih' :
              (∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
                ∑ r ∈ T,
                  ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
            simpa only [hT] using ih
          rw [ih', hcard]
          have hself : Nat.lcm (p ^ R) (p ^ R) = p ^ R := by simp
          rw [hself]
          norm_num only [Nat.cast_pow]
          have hweight : 2 * R - 3 = 2 * A + 1 := by
            dsimp only [R]
            omega
          rw [hweight]
          push_cast
          ring

theorem sum_highExponents_pair_inv_lcm_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  rw [sum_highExponents_pair_inv_lcm_eq_diagonalWeight]
  calc
    (∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hden : 0 ≤ (p : ℝ) ^ r := by positivity
        have hw : 0 ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
        have hr0 : 0 ≤ (r : ℝ) := by positivity
        calc
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r =
              ((2 * r - 3 : ℕ) : ℝ) *
                (1 / (p : ℝ) ^ r) := by ring
          _ ≤ ((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
            apply mul_le_mul_of_nonneg_left _ hw
            exact div_le_div_of_nonneg_right (by linarith) hden
    _ ≤ quadraticHalfMass / (p : ℝ) ^ 2 :=
      sum_diagonalWeight_raddone_inv_pow_le hp.two_le

theorem sum_highExponents_pair_inv_product_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) ≤
      4 / (p : ℝ) ^ 4 := by
  have htail :
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) ≤
        2 / (p : ℝ) ^ 2 := by
    simpa only [highExponents] using
      (sum_inv_pow_tail_le (p := p) (r := 1) (A := A) hp.two_le)
  have htail0 :
      0 ≤ ∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ) := by positivity
  calc
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) =
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents A, 1 / ((p ^ l : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          norm_num only [Nat.cast_mul]
          ring
    _ ≤ (2 / (p : ℝ) ^ 2) * (2 / (p : ℝ) ^ 2) :=
      mul_le_mul htail htail htail0 (by positivity)
    _ = 4 / (p : ℝ) ^ 4 := by ring

end
end Erdos390.Full.PrimePowerLcmGeometry

-- ===== from Full/PaperBridgePhysicalPowerCorrectionRow.lean =====
open scoped BigOperators
open Filter Topology
namespace Erdos390.Full.PaperBridgeFit
noncomputable section
open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry
namespace BridgeData
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)
set_option maxHeartbeats 2000000 in
private theorem expect_finset_sum
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (S : Finset ℕ)
    (f : ℕ → Omega → ℝ) :
    mu.expect (fun x ↦ ∑ k ∈ S, f k x) =
      ∑ k ∈ S, mu.expect (f k) := by
  induction S using Finset.induction_on with
  | empty => simp [FiniteProbability.expect_zero]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [mu.expect_add, ih]

private theorem sum_pair_linear
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J)
    (a b : I → J → ℝ) (c d : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
      c * (∑ i ∈ S, ∑ j ∈ T, a i j) +
        d * (∑ i ∈ S, ∑ j ∈ T, b i j) := by
  calc
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
        ∑ i ∈ S,
          (c * (∑ j ∈ T, a i j) + d * (∑ j ∈ T, b i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

private theorem sum_bandPrime_inv_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ)) =
      bandReciprocalSum n W := by
  unfold bandReciprocalSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ)))

private theorem sum_bandPrime_inv_sq_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ) ^ 2) =
      bandReciprocalSquareSum n W := by
  unfold bandReciprocalSquareSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ) ^ 2))

theorem expect_J_le_of_divisor_fallback
    {Omega : Type*} [Fintype Omega] {M p : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime)
    {G : ℝ} (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      law.probability.expect (fun x ↦ divInd D (law.value x)) ≤
        G * (1 / (D : ℝ))) :
    law.probability.expect (law.J p) ≤ 2 * G * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum law hp]
  rw [expect_finset_sum]
  calc
    (∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.expect (law.Ip p k)) ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          G * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = G * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ G * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hG
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * G * (1 / (p : ℝ)) ^ 2 := by ring

theorem abs_expect_J_sub_le_of_divisor_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {d : ℝ} (hd : 0 ≤ d)
    (hdiv : ∀ D : ℕ, 0 < D →
      |nu.probability.expect (fun x ↦ divInd D (nu.value x)) -
        mu.probability.expect (fun x ↦ divInd D (mu.value x))| ≤
          d * (1 / (D : ℝ))) :
    |nu.probability.expect (nu.J p) -
      mu.probability.expect (mu.J p)| ≤
        2 * d * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum nu hp, J_eq_valuationCutoff_sum mu hp]
  rw [expect_finset_sum, expect_finset_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.expect (nu.Ip p k) -
          mu.probability.expect (mu.Ip p k))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.expect (nu.Ip p k) -
            mu.probability.expect (mu.Ip p k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
          d * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = d * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ d * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hd
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * d * (1 / (p : ℝ)) ^ 2 := by ring

theorem abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p q - mu.covJI p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I q) -
          mu.probability.covariance (mu.Ip p k) (mu.I q))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G + 3 * G ^ 2) *
          (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcop : Nat.Coprime (p ^ k) (q ^ 1) :=
        Nat.coprime_pow_primes k 1 hp hq hpq
      have hlcm : Nat.lcm (p ^ k) q = p ^ k * q := by
        simpa only [pow_one] using hcop.lcm_eq_mul
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) q : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (q : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) q (pow_pos hp.pos k) hq.pos
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
          rw [hlcm, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring

theorem abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p p - mu.covJI p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I p) -
          mu.probability.covariance (mu.Ip p k) (mu.I p))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
          3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
            (1 / (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := (mem_highExponents.mp hk).1
      have hlcm : Nat.lcm (p ^ k) p = p ^ k :=
        Nat.lcm_eq_left_iff_dvd.mpr (dvd_pow_self p (by omega))
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) p : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (p : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) p (pow_pos hp.pos k) hp.pos
        _ = e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
            3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / (p : ℝ))) := by rw [hlcm]; ring
    _ = e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by ring

theorem abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p q - mu.covIJ p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by
  have hcovSwap : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
    exact hcov
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    nu mu hq hp hpq.symm he hG hcovSwap
  have hnu : nu.covIJ p q = nu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p q = mu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  rw [hnu, hmu]
  convert hraw using 1
  ring

theorem abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p p - mu.covIJ p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    nu mu hp he hG hcov
  have hnu : nu.covIJ p p = nu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p p = mu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  simpa only [hnu, hmu] using hraw

theorem abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p q - mu.covJJ p q| ≤
      e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hq,
    covJJ_eq_valuationCutoff_sum mu hp hq,
    ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        ((∑ l ∈ highExponents (valuationCutoff q M),
            nu.probability.covariance (nu.Ip p k) (nu.Ip q l)) -
          ∑ l ∈ highExponents (valuationCutoff q M),
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
              nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            ∑ l ∈ highExponents (valuationCutoff q M),
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
            (nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hcop : Nat.Coprime (p ^ k) (q ^ l) :=
        Nat.coprime_pow_primes k l hp hq hpq
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((q ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (q ^ l) (pow_pos hp.pos k) (pow_pos hq.pos l)
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
          rw [hcop.lcm_eq_mul, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2)) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents (valuationCutoff q M),
          1 / ((q ^ l : ℕ) : ℝ)) := by
      calc
        (∑ k ∈ highExponents (valuationCutoff p M),
          ∑ l ∈ highExponents (valuationCutoff q M),
            e * (G + 3 * G ^ 2) *
              (1 / ((p ^ k : ℕ) : ℝ)) *
                (1 / ((q ^ l : ℕ) : ℝ))) =
            ∑ k ∈ highExponents (valuationCutoff p M),
              (e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
                (∑ l ∈ highExponents (valuationCutoff q M),
                  1 / ((q ^ l : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
        _ = (∑ k ∈ highExponents (valuationCutoff p M),
              e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
              (∑ l ∈ highExponents (valuationCutoff q M),
                1 / ((q ^ l : ℕ) : ℝ)) := by
            rw [Finset.sum_mul]
        _ = _ := by
            rw [← Finset.mul_sum]
    _ ≤ (e * (G + 3 * G ^ 2)) *
        (2 / (p : ℝ) ^ 2) * (2 / (q : ℝ) ^ 2) := by
      have hpTail := sum_inv_pow_tail_le (p := p) (r := 1)
        (A := valuationCutoff p M) hp.two_le
      have hqTail := sum_inv_pow_tail_le (p := q) (r := 1)
        (A := valuationCutoff q M) hq.two_le
      have hcoef : 0 ≤ e * (G + 3 * G ^ 2) := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (by simpa only [highExponents] using hpTail)
          hcoef)
        (by simpa only [highExponents] using hqTail)
        (by positivity) (by positivity)
    _ = e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring

theorem abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p p - mu.covJJ p p| ≤
      e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hp,
    covJJ_eq_valuationCutoff_sum mu hp hp,
    ← Finset.sum_sub_distrib]
  let S := highExponents (valuationCutoff p M)
  calc
    |∑ k ∈ S,
        ((∑ l ∈ S, nu.probability.covariance (nu.Ip p k) (nu.Ip p l)) -
          ∑ l ∈ S,
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| ≤
        ∑ k ∈ S,
          |∑ l ∈ S,
              nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            ∑ l ∈ S,
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ S,
          |∑ l ∈ S,
            (nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
          |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
        e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
          3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((p ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (p ^ l) (pow_pos hp.pos k) (pow_pos hp.pos l)
        _ = e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
            3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
          rw [Nat.cast_mul]
          ring
    _ = e * (G *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
        3 * G ^ 2 *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      have hlin := sum_pair_linear S S
        (fun k l ↦ 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))
        (fun k l ↦ 1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))
        (e * G) (e * (3 * G ^ 2))
      convert hlin using 1 <;> ring
    _ ≤ e * (G * (quadraticHalfMass / (p : ℝ) ^ 2) +
        3 * G ^ 2 * (4 / (p : ℝ) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_lcm_le
                (p := p) (A := valuationCutoff p M) hp)) hG
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_product_le
                (p := p) (A := valuationCutoff p M) hp)) (by positivity)
      · exact he
    _ = e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by ring

theorem sum_abs_covJI_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

theorem sum_abs_covIJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

theorem sum_abs_covJJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|) ≤
      e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W +
        e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
          12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (4 * G + 12 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤
      e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 4 * G + 12 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

theorem sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
    {Cell : Type*} [Fintype Cell]
    {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
    {M n W : ℕ}
    (weight : FiniteProbability Cell)
    (mu nu : ∀ c, BoundedValuationLaw (Omega c) M)
    (p : BandPrime n W)
    {epsilon G : ℝ} (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G)
    (hW : 1 < W)
    (hbase : ∀ c D, 0 < D →
      (mu c).probability.expect
          (fun x ↦ divInd D ((mu c).value x)) ≤
        G * (1 / (D : ℝ)))
    (hdiff : ∀ c D, 0 < D →
      |(nu c).probability.expect
            (fun x ↦ divInd D ((nu c).value x)) -
        (mu c).probability.expect
            (fun x ↦ divInd D ((mu c).value x))| ≤
          (8 * epsilon) * G * (1 / (D : ℝ)))
    (hcov : ∀ c D E, 0 < D → 0 < E →
      |(nu c).probability.covariance
            (fun x ↦ divInd D ((nu c).value x))
            (fun x ↦ divInd E ((nu c).value x)) -
        (mu c).probability.covariance
            (fun x ↦ divInd D ((mu c).value x))
            (fun x ↦ divInd E ((mu c).value x))| ≤
        (8 * epsilon) *
          (G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    (∑ q : BandPrime n W,
      |(Nu.covVV p.1 q.1 - Nu.covII p.1 q.1) -
        (Mu.covVV p.1 q.1 - Mu.covII p.1 q.1)|) ≤
      physicalPowerCorrectionMixtureBudget epsilon G n W p.1 := by
  dsimp only
  let e : ℝ := 8 * epsilon
  let H : ℝ := bandReciprocalSum n W
  let S₂ : ℝ := bandReciprocalSquareSum n W
  let w₁ : ℝ := 1 / (W : ℝ)
  let p₁ : ℝ := 1 / (p.1 : ℝ)
  let AIp := G * p₁
  let AJp := 2 * G * p₁ ^ 2
  let AIrow := G * H
  let AJrow := 2 * G * w₁
  let dIp := e * G * p₁
  let dJp := 2 * e * G * p₁ ^ 2
  let dIrow := e * G * H
  let dJrow := 2 * e * G * w₁
  let dJI := e * (2 * G + 6 * G ^ 2) * p₁ ^ 2 * H +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dIJ := e * (2 * G + 6 * G ^ 2) * p₁ * S₂ +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dJJ := e * (4 * G + 12 * G ^ 2) * p₁ ^ 2 * S₂ +
    e * (G * quadraticHalfMass * p₁ ^ 2 + 12 * G ^ 2 * p₁ ^ 4)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hH : 0 ≤ H := by dsimp only [H, bandReciprocalSum]; positivity
  have hS₂ : 0 ≤ S₂ := by
    dsimp only [S₂, bandReciprocalSquareSum]
    positivity
  have hw₁ : 0 ≤ w₁ := by dsimp only [w₁]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp only [p₁]; positivity
  have hAIp : 0 ≤ AIp := by dsimp only [AIp]; positivity
  have hAJp : 0 ≤ AJp := by dsimp only [AJp]; positivity
  have hAIrow : 0 ≤ AIrow := by dsimp only [AIrow]; positivity
  have hAJrow : 0 ≤ AJrow := by dsimp only [AJrow]; positivity
  have hdIp0 : 0 ≤ dIp := by dsimp only [dIp]; positivity
  have hdJp0 : 0 ≤ dJp := by dsimp only [dJp]; positivity
  have hIpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).I p.1)| ≤ AIp := by
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).I p.1)
      ((mu c).I_nonneg p.1)
    rw [abs_of_nonneg hnonneg]
    simpa only [BoundedValuationLaw.I, AIp, p₁, mul_assoc] using
      hbase c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).J p.1)| ≤ AJp := by
    have hpPrime := prime_of_mem_primeBand p.2
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).J p.1)
      ((mu c).J_nonneg hpPrime)
    rw [abs_of_nonneg hnonneg]
    simpa only [AJp, p₁] using
      expect_J_le_of_divisor_fallback (mu c) hpPrime hG (hbase c)
  have hIqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).I q.1)|) ≤ AIrow := by
    calc
      _ = ∑ q : BandPrime n W,
          (mu c).probability.expect ((mu c).I q.1) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).I_nonneg q.1))]
      _ ≤ ∑ q : BandPrime n W, G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I] using
          hbase c q.1 (prime_of_mem_primeBand q.2).pos
      _ = AIrow := by
        dsimp only [AIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).J q.1)|) ≤ AJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hqPrime := prime_of_mem_primeBand q.2
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).J_nonneg hqPrime))]
        exact expect_J_le_of_divisor_fallback
          (mu c) hqPrime hG (hbase c)
      _ = 2 * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ AJrow := by
        dsimp only [AJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hIpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).I p.1) -
        (mu c).probability.expect ((mu c).I p.1)| ≤ dIp := by
    simpa only [BoundedValuationLaw.I, dIp, e, p₁, mul_assoc] using
      hdiff c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).J p.1) -
        (mu c).probability.expect ((mu c).J p.1)| ≤ dJp := by
    have hraw := abs_expect_J_sub_le_of_divisor_difference
        (nu c) (mu c) (prime_of_mem_primeBand p.2)
          (mul_nonneg he hG) (by
            intro D hD
            dsimp only [e]
            simpa only [mul_assoc] using hdiff c D hD)
    dsimp only [dJp, e, p₁]
    convert hraw using 1
    ring
  have hIqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).I q.1) -
          (mu c).probability.expect ((mu c).I q.1)|) ≤ dIrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          e * G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I, e, mul_assoc] using
          hdiff c q.1 (prime_of_mem_primeBand q.2).pos
      _ = dIrow := by
        dsimp only [dIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).J q.1) -
          (mu c).probability.expect ((mu c).J q.1)|) ≤ dJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * e * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [mul_assoc] using
          abs_expect_J_sub_le_of_divisor_difference
            (nu c) (mu c) (prime_of_mem_primeBand q.2)
              (mul_nonneg he hG) (by
                intro D hD
                dsimp only [e]
                simpa only [mul_assoc] using hdiff c D hD)
      _ = 2 * e * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * e * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * e * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ dJrow := by
        dsimp only [dJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hJI (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJI p.1 q.1 - (mu c).covJI p.1 q.1|) ≤ dJI := by
    simpa only [dJI, e, H, p₁] using
      sum_abs_covJI_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hIJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covIJ p.1 q.1 - (mu c).covIJ p.1 q.1|) ≤ dIJ := by
    simpa only [dIJ, e, S₂, p₁] using
      sum_abs_covIJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hJJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJJ p.1 q.1 - (mu c).covJJ p.1 q.1|) ≤ dJJ := by
    simpa only [dJJ, e, S₂, p₁] using
      sum_abs_covJJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hmix :=
    FiniteProbability.sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
      weight mu nu p.1 (fun q : BandPrime n W ↦ q.1)
      hAIp hAJp hAIrow hAJrow hdIp0 hdJp0
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJI hIJ hJJ
  simpa only [physicalPowerCorrectionMixtureBudget, e, H, S₂, w₁,
    p₁, AIp, AJp, AIrow, AJrow, dIp, dJp, dIrow, dJrow,
    dJI, dIJ, dJJ] using hmix

theorem ee0b_main
    [Nonempty Head]
    (xi : B.ParamSpace)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys G : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hG : 0 ≤ G) (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ G)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
      physicalPowerCorrectionMixtureBudget
        (Aphys * Kphys / B.L) G
          B.sampleData.n B.sampleData.W p.1 := by
  let weight : FiniteProbability (Cell Head) :=
    tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
  let mu := B.mediumComponentValuationLaw xi
  let nu := B.actualComponentValuationLaw xi
  let epsilon := Aphys * Kphys / B.L
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hbase (c : Cell Head) (D : ℕ) (hD : 0 < D) :
      (mu c).probability.expect (fun x ↦ divInd D ((mu c).value x)) ≤
        G * (1 / (D : ℝ)) := by
    have hraw := B.cellMediumLaw_expect_divInd_le xi c
      hD hA hW (hrho c) (hcard c) heta
    have hGc0 : 0 ≤ Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c := by
      exact div_nonneg (Real.exp_pos _).le (hrho c).le
    change (B.cellMediumLaw xi c).expect (fun x ↦ divInd D (x : ℕ)) ≤ _
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
            (rho c * (D : ℝ)) := hraw
      _ = (Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) / rho c) *
            (1 / (D : ℝ)) := by ring
      _ ≤ G * (1 / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (hGdom c) (by positivity)
  have hdiff (c : Cell Head) (D : ℕ) (hD : 0 < D) :
      |(nu c).probability.expect (fun x ↦ divInd D ((nu c).value x)) -
        (mu c).probability.expect (fun x ↦ divInd D ((mu c).value x))| ≤
          8 * epsilon * G * (1 / (D : ℝ)) := by
    have hraw := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hD hA hW (hrho c) (hcard c) heta hAphys0 hKphys0
        hAphys (hKphys c) hsmall
    have hfactor0 : 0 ≤ 8 * epsilon * (1 / (D : ℝ)) := by positivity
    simpa only [nu, mu, actualComponentValuationLaw_probability,
      actualComponentValuationLaw_value,
      mediumComponentValuationLaw_probability,
      mediumComponentValuationLaw_value, epsilon, mul_assoc] using
      hraw.trans (by
        nlinarith [mul_le_mul_of_nonneg_left (hGdom c) hfactor0])
  have hcov (c : Cell Head) (D E : ℕ) (hD : 0 < D) (hE : 0 < E) :
      |(nu c).probability.covariance
            (fun x ↦ divInd D ((nu c).value x))
            (fun x ↦ divInd E ((nu c).value x)) -
        (mu c).probability.covariance
            (fun x ↦ divInd D ((mu c).value x))
            (fun x ↦ divInd E ((mu c).value x))| ≤
        8 * epsilon *
          (G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
    have hraw := B.abs_guardedCell_fullTilt_divIndCovariance_sub_medium_le
      xi c hD hE hA hW (hrho c) (hcard c) heta hAphys0 hKphys0
        hAphys (hKphys c) hsmall
    let Gc := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho c
    have hGc0 : 0 ≤ Gc := by
      dsimp only [Gc]
      exact div_nonneg (Real.exp_pos _).le (hrho c).le
    have hinside :
        Gc * (1 / (Nat.lcm D E : ℝ)) +
            3 * (Gc * (1 / (D : ℝ))) * (Gc * (1 / (E : ℝ))) ≤
          G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))) := by
      have hGcG : Gc ≤ G := by simpa only [Gc] using hGdom c
      have hlinear := mul_le_mul_of_nonneg_right hGcG (by positivity :
        0 ≤ (1 / (Nat.lcm D E : ℝ)))
      have hDmul := mul_le_mul_of_nonneg_right hGcG
        (by positivity : 0 ≤ (1 / (D : ℝ)))
      have hEmul := mul_le_mul_of_nonneg_right hGcG
        (by positivity : 0 ≤ (1 / (E : ℝ)))
      have hprod := mul_le_mul hDmul hEmul
        (mul_nonneg hGc0 (by positivity)) (mul_nonneg hG (by positivity))
      linarith
    have hscale0 : 0 ≤ 8 * epsilon := by positivity
    simpa only [nu, mu, actualComponentValuationLaw_probability,
      actualComponentValuationLaw_value,
      mediumComponentValuationLaw_probability,
      mediumComponentValuationLaw_value, epsilon, Gc] using
      hraw.trans (mul_le_mul_of_nonneg_left hinside hscale0)
  have hmix := sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
    weight mu nu p hepsilon hG hW hbase hdiff hcov
  have hactual := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hactual
  simpa only [weight, mu, nu, epsilon, physicalMediumReferenceLaw,
    hactual] using hmix

end BridgeData
end
end Erdos390.Full.PaperBridgeFit


set_option maxHeartbeats 4000000 in
open BigOperators in
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3)
  [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
  (rho : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head → Real) {A Aphys Kphys G : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Aphys →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Kphys →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) G →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                  B)) →
            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (rho c)) →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho c)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Finset.card.{0} Nat
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          c)))) →
                (∀
                    (r :
                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))),
                    @LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} Head Band inst
                          inst_1 inst_2 inst_3 B xi r))
                      A) →
                  @LE.le.{0}
                      ((fun
                            (x :
                              @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                inst_3 B) =>
                          Real)
                        (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)))
                      Real.instLE
                      (@abs.{0}
                        ((fun
                              (x :
                                @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                  inst_3 B) =>
                            Real)
                          (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)))
                        Real.lattice Real.instAddGroup
                        (@WithLp.ofLp.{max u_1 u_2}
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          ((i :
                              @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                inst_3 B) →
                            (fun
                                  (x :
                                    @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1
                                      inst_2 inst_3 B) =>
                                Real)
                              i)
                          xi
                          (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))))
                      Aphys →
                    (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            c),
                        @LE.le.{0} Real Real.instLE
                          (@abs.{0} Real Real.lattice Real.instAddGroup
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} Head Band inst inst_1
                              inst_2 inst_3 B
                              (@Sigma.mk.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c m)))
                          Kphys) →
                      @LE.le.{0} Real Real.instLE
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Aphys Kphys)
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                                B)))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                            @LE.le.{0} Real Real.instLE
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (Real.exp
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) A
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1
                                          inst_2 inst_3 B))
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (Real.log
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)
                                              (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))))
                                        (Real.log
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))))))))
                                (rho c))
                              G) →
                          ∀
                            (p :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))),
                            @LE.le.{0} Real Real.instLE
                              (@Finset.sum.{0, 0}
                                (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B)))
                                Real Real.instAddCommMonoid
                                (@Finset.univ.{0}
                                  (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))))
                                fun
                                  (q :
                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))) =>
                                @abs.{0} Real Real.lattice Real.instAddGroup
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} Head
                                          Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q))
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} Head
                                          Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q)))
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalMediumReferenceLaw.{u_1, u_2}
                                          Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q))
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalMediumReferenceLaw.{u_1, u_2}
                                          Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q)))))
                              (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Aphys Kphys)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2
                                    inst_3 B))
                                G
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Subtype.val.{1} Nat
                                  (fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      (Erdos390.Full.ArithmeticModel.primeBand
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B)))
                                      p)
                                  p)) := by
  intro Head Band _ _ _ _ B _ xi rho A Aphys Kphys G hA hAphys0 hKphys0 hG hW hrho hcard heta hAphys hKphys hsmall hGdom p
  exact Erdos390.Full.PaperBridgeFit.BridgeData.ee0b_main B xi rho hA hAphys0 hKphys0 hG hW hrho hcard heta hAphys hKphys
    hsmall hGdom p
