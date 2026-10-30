-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.model_sum_two_term_asymp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:48:06.088975+00:00
-- url     : https://prove2.me/submissions/fcfbf32f-16f4-4b34-8ea8-468d5880c69a

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_abs_add_five_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_sq
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_sum_eq_moments
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_le_power_sharp
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_nonneg
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_one_two_term
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_three_one_term
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_two_asymp_weak
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

/-! ### Small lemmas -/

/-! ### Two-term asymptotic from the moment asymptotics -/

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000
open Filter Finset
open scoped Topology BigOperators
set_option maxHeartbeats 8000000 in
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |(∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
        - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    exact massLam_pos
  have hlam_sq : lam ^ 2 = Real.pi ^ 2 / 6 := by
    rw [hlamdef, massLam_sq]
  have hCpos : 0 < C := C_pos
  have hCeq : C = 2 * lam := by
    rw [hlamdef, massLam]
    ring
  obtain ⟨K1, hK1pos, hK1⟩ := sigmaMoment_one_two_term
  set K2 : ℝ :=
    3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6
    with hK2def
  set K3 : ℝ :=
    2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24
    with hK3def
  have hden_exp : 0 < 1 - Real.exp (-1) := by
    have hlt : Real.exp (-1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  have hK2pos : 0 < K2 := by
    rw [hK2def]
    positivity
  have hK3pos : 0 < K3 := by
    rw [hK3def]
    positivity
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  set C1c : ℝ := 3 / (2 * lam) with hC1c
  set C2c : ℝ := 15 / (8 * lam ^ 3) with hC2c
  set C3c : ℝ := 3 / (8 * lam ^ 4) + 3 * C / (16 * lam ^ 4) with hC3c
  set C4c : ℝ := 3 * C / (64 * lam ^ 6) with hC4c
  set K_total : ℝ := K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + 9 / lam ^ 3 + 1
    with hKtotal
  have hK_total_pos : 0 < K_total := by
    have hC1nn : 0 ≤ C1c := by rw [hC1c]; positivity
    have hC2nn : 0 ≤ C2c := by rw [hC2c]; positivity
    have hC3nn : 0 ≤ C3c := by rw [hC3c]; positivity
    have hC4nn : 0 ≤ C4c := by rw [hC4c]; positivity
    have hB5nn : 0 ≤ 9 / lam ^ 3 := by positivity
    have hbase : 0 ≤ K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + 9 / lam ^ 3 := by
      nlinarith [mul_nonneg hK1pos.le hC1nn, mul_nonneg hK2pos.le hC2nn,
        mul_nonneg hK3pos.le hC3nn, mul_nonneg hK4nn hC4nn, hB5nn]
    rw [hKtotal]
    linarith
  refine ⟨K_total, hK_total_pos, ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ lam ^ 2 < (n : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max 1 (⌈lam ^ 2⌉₊ + 1), ?_⟩
    intro n hn
    constructor
    · exact le_trans (le_max_left _ _) hn
    · have hceil_nat : ⌈lam ^ 2⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
      have hceil_real : (⌈lam ^ 2⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by
        have hceil_real' : ((⌈lam ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hceil_nat
        simpa using hceil_real'
      have hceil_le : lam ^ 2 ≤ (⌈lam ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      linarith
  filter_upwards [hev] with n hn
  rcases hn with ⟨hn1, hnlam_lt⟩
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n:ℝ) := by
    rw [hsdef]
    exact Real.sq_sqrt hnpos.le
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    positivity
  have hlam_lt_s : lam < s := by
    have hsq : lam ^ 2 < s ^ 2 := by
      rw [hs2]
      exact hnlam_lt
    nlinarith [hlam0, hs0]
  have htlt1 : t < 1 := by
    rw [htdef, div_lt_one hs0]
    exact hlam_lt_s
  have htle1 : t ≤ 1 := le_of_lt htlt1
  have hM1raw := hK1 t ht0 htlt1
  have hM1n :
      |sigmaMoment 1 t - (2 * lam ^ 2 / t ^ 3 - 1 / (2 * t ^ 2))| ≤ K1 / t := by
    simpa [hlam_sq] using hM1raw
  have hM2raw := sigmaMoment_two_asymp_weak (t := t) ht0 htle1
  have hM2n :
      |sigmaMoment 2 t - 6 * lam ^ 2 / t ^ 4| ≤ K2 / t ^ 3 := by
    simpa [hK2def, hlam_sq] using hM2raw
  have hM3raw := sigmaMoment_three_one_term (t := t) ht0 htle1
  have hM3n :
      |sigmaMoment 3 t - 24 * lam ^ 2 / t ^ 5| ≤ K3 / t ^ 4 := by
    simpa [hK3def, hlam_sq] using hM3raw
  have hM4n : sigmaMoment 4 t ≤ K4 / t ^ 6 := by
    simpa using hK4 t ht0 htle1
  rw [model_sum_eq_moments n hn1]
  rw [← hlamdef, ← hsdef, ← htdef]
  set mu0 : ℝ := 3 / lam with hmu0
  set mu1 : ℝ := 3 / (2 * lam ^ 2) with hmu1
  set c1 : ℝ := 3 / (2 * (n:ℝ) * s) with hc1
  set c2 : ℝ := 15 / (8 * (n:ℝ) ^ 2 * s) with hc2
  set c3 : ℝ := 3 / (8 * (n:ℝ) ^ 2 * s ^ 3) - 3 * C / (16 * (n:ℝ) ^ 3) with hc3
  set c4 : ℝ := -3 * C / (64 * (n:ℝ) ^ 4) with hc4
  set M1a : ℝ := 2 * lam ^ 2 / t ^ 3 - 1 / (2 * t ^ 2) with hM1a
  set M2a : ℝ := 6 * lam ^ 2 / t ^ 4 with hM2a
  set M3a : ℝ := 24 * lam ^ 2 / t ^ 5 with hM3a
  have hM1err : |sigmaMoment 1 t - M1a| ≤ K1 / t := by
    simpa [hM1a] using hM1n
  have hM2err : |sigmaMoment 2 t - M2a| ≤ K2 / t ^ 3 := by
    simpa [hM2a] using hM2n
  have hM3err : |sigmaMoment 3 t - M3a| ≤ K3 / t ^ 4 := by
    simpa [hM3a] using hM3n
  have hcancel :
      c1 * M1a + c2 * M2a + c3 * M3a - (mu0 + mu1 / s)
        = (9 / lam ^ 3) / (n : ℝ) := by
    rw [hc1, hc2, hc3, hM1a, hM2a, hM3a, hmu0, hmu1, htdef, hCeq, ← hs2]
    field_simp [hlam0.ne', hs0.ne']
    ring
  have hrewrite :
      (c1 * sigmaMoment 1 t + c2 * sigmaMoment 2 t
        + (c3 * sigmaMoment 3 t + c4 * sigmaMoment 4 t))
        - (mu0 + mu1 / s)
      = c1 * (sigmaMoment 1 t - M1a)
        + c2 * (sigmaMoment 2 t - M2a)
        + c3 * (sigmaMoment 3 t - M3a)
        + c4 * sigmaMoment 4 t
        + (9 / lam ^ 3) / (n : ℝ) := by
    rw [← hcancel]
    ring
  rw [hrewrite]
  have hc1nn : 0 ≤ c1 := by rw [hc1]; positivity
  have hc2nn : 0 ≤ c2 := by rw [hc2]; positivity
  have hsge1 : 1 ≤ s := by
    have hs2ge : 1 ≤ s ^ 2 := by
      rw [hs2]
      exact_mod_cast hn1
    exact ((one_le_sq_iff_one_le_abs s).1 hs2ge).trans_eq (abs_of_pos hs0)
  have hcoef1 : |c1| * (K1 / t) ≤ (K1 * C1c) / (n : ℝ) := by
    have hdiv : |c1| / t = C1c / (n : ℝ) := by
      rw [abs_of_nonneg hc1nn, hc1, hC1c, htdef, ← hs2]
      field_simp [hlam0.ne', hs0.ne']
    apply le_of_eq
    calc
      |c1| * (K1 / t) = K1 * (|c1| / t) := by ring
      _ = K1 * (C1c / (n : ℝ)) := by rw [hdiv]
      _ = (K1 * C1c) / (n : ℝ) := by ring
  have hcoef2 : |c2| * (K2 / t ^ 3) ≤ (K2 * C2c) / (n : ℝ) := by
    have hdiv : |c2| / t ^ 3 = C2c / (n : ℝ) := by
      rw [abs_of_nonneg hc2nn, hc2, hC2c, htdef, ← hs2]
      field_simp [hlam0.ne', hs0.ne']
    apply le_of_eq
    calc
      |c2| * (K2 / t ^ 3) = K2 * (|c2| / t ^ 3) := by ring
      _ = K2 * (C2c / (n : ℝ)) := by rw [hdiv]
      _ = (K2 * C2c) / (n : ℝ) := by ring
  have hcoef3 : |c3| * (K3 / t ^ 4) ≤ (K3 * C3c) / (n : ℝ) := by
    have hdiv : |c3| / t ^ 4 ≤ C3c / (n : ℝ) := by
      set a : ℝ := 3 / (8 * (n:ℝ) ^ 2 * s ^ 3) with ha
      set b : ℝ := 3 * C / (16 * (n:ℝ) ^ 3) with hb
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have hb0 : 0 ≤ b := by rw [hb]; positivity
      have habs : |c3| ≤ a + b := by
        have hc3ab : c3 = a - b := by rw [ha, hb, hc3]
        rw [hc3ab, abs_le]
        constructor <;> linarith only [ha0, hb0]
      have hA_le : 3 / (8 * lam ^ 4 * s ^ 3) ≤ 3 / (8 * lam ^ 4 * s ^ 2) := by
        have hs2_le_s3 : s ^ 2 ≤ s ^ 3 := by
          calc
            s ^ 2 = s ^ 2 * 1 := by ring
            _ ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hsge1 (by positivity)
            _ = s ^ 3 := by ring
        have hden : 8 * lam ^ 4 * s ^ 2 ≤ 8 * lam ^ 4 * s ^ 3 :=
          mul_le_mul_of_nonneg_left hs2_le_s3 (by positivity)
        exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 3) (by positivity) hden
      calc
        |c3| / t ^ 4 ≤ (a + b) / t ^ 4 := by gcongr
        _ = 3 / (8 * lam ^ 4 * s ^ 3) + 3 * C / (16 * lam ^ 4 * s ^ 2) := by
          rw [ha, hb, htdef, ← hs2]
          field_simp [hlam0.ne', hs0.ne']
        _ ≤ 3 / (8 * lam ^ 4 * s ^ 2) + 3 * C / (16 * lam ^ 4 * s ^ 2) := by
          linarith only [hA_le]
        _ = C3c / (n : ℝ) := by
          rw [hC3c, ← hs2]
          field_simp [hlam0.ne', hs0.ne']
    calc
      |c3| * (K3 / t ^ 4) = K3 * (|c3| / t ^ 4) := by ring
      _ ≤ K3 * (C3c / (n : ℝ)) := mul_le_mul_of_nonneg_left hdiv hK3pos.le
      _ = (K3 * C3c) / (n : ℝ) := by ring
  have hcoef4 : |c4| * (K4 / t ^ 6) ≤ (K4 * C4c) / (n : ℝ) := by
    have hc4_abs : |c4| = 3 * C / (64 * (n : ℝ) ^ 4) := by
      rw [hc4]
      have hnonneg : 0 ≤ 3 * C / (64 * (n : ℝ) ^ 4) := by positivity
      rw [show -3 * C / (64 * (n : ℝ) ^ 4)
          = -(3 * C / (64 * (n : ℝ) ^ 4)) by ring]
      rw [abs_neg, abs_of_nonneg hnonneg]
    have hdiv : |c4| / t ^ 6 = C4c / (n : ℝ) := by
      rw [hc4_abs, hC4c, htdef, ← hs2]
      field_simp [hlam0.ne', hs0.ne']
    apply le_of_eq
    calc
      |c4| * (K4 / t ^ 6) = K4 * (|c4| / t ^ 6) := by ring
      _ = K4 * (C4c / (n : ℝ)) := by rw [hdiv]
      _ = (K4 * C4c) / (n : ℝ) := by ring
  calc
    |c1 * (sigmaMoment 1 t - M1a)
        + c2 * (sigmaMoment 2 t - M2a)
        + c3 * (sigmaMoment 3 t - M3a)
        + c4 * sigmaMoment 4 t
        + (9 / lam ^ 3) / (n : ℝ)|
        ≤ |c1 * (sigmaMoment 1 t - M1a)|
          + |c2 * (sigmaMoment 2 t - M2a)|
          + |c3 * (sigmaMoment 3 t - M3a)|
          + |c4 * sigmaMoment 4 t|
          + |(9 / lam ^ 3) / (n : ℝ)| := by
            exact abs_add_five_le _ _ _ _ _
    _ = |c1| * |sigmaMoment 1 t - M1a|
          + |c2| * |sigmaMoment 2 t - M2a|
          + |c3| * |sigmaMoment 3 t - M3a|
          + |c4| * sigmaMoment 4 t
          + (9 / lam ^ 3) / (n : ℝ) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            rw [abs_of_nonneg (sigmaMoment_nonneg 4 t ht0)]
            rw [abs_of_nonneg (by positivity : 0 ≤ (9 / lam ^ 3) / (n : ℝ))]
    _ ≤ |c1| * (K1 / t)
          + |c2| * (K2 / t ^ 3)
          + |c3| * (K3 / t ^ 4)
          + |c4| * (K4 / t ^ 6)
          + (9 / lam ^ 3) / (n : ℝ) := by
            have b1 := mul_le_mul_of_nonneg_left hM1err (abs_nonneg c1)
            have b2 := mul_le_mul_of_nonneg_left hM2err (abs_nonneg c2)
            have b3 := mul_le_mul_of_nonneg_left hM3err (abs_nonneg c3)
            have b4 := mul_le_mul_of_nonneg_left hM4n (abs_nonneg c4)
            linarith only [b1, b2, b3, b4]
    _ ≤ (K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + 9 / lam ^ 3) / (n : ℝ) := by
            have hsplit :
                (K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + 9 / lam ^ 3) / (n : ℝ)
                  = (K1 * C1c) / (n : ℝ) + (K2 * C2c) / (n : ℝ)
                    + (K3 * C3c) / (n : ℝ) + (K4 * C4c) / (n : ℝ)
                    + (9 / lam ^ 3) / (n : ℝ) := by
              ring
            rw [hsplit]
            linarith only [hcoef1, hcoef2, hcoef3, hcoef4]
    _ ≤ K_total / (n : ℝ) := by
            have hleK :
                K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + 9 / lam ^ 3 ≤ K_total := by
              rw [hKtotal]
              linarith
            exact div_le_div_of_nonneg_right hleK hnpos.le
