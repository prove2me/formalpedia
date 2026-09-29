-- Prove2me | solution 1 for BanditAlgorithm.jao_collapsed_bandit_regret_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T17:42:38.836631+00:00
-- url     : https://prove2.me/submissions/222a6ad1-7741-40ee-b8e8-a2466ba2c745

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem solution
    (m : ℕ) (hm : 20 ≤ m) (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (T : ℕ) (hT : (16 : ℝ) * m ≤ δ * T)
    (hε : ε = 1 / 5 * Real.sqrt (δ * m / T))
    (V R : Fin m → ℝ) (hV0 : ∀ b, 0 ≤ V b)
    (hVsum : ∑ b, V b ≤ (T : ℝ) / 2 + 1 / (2 * δ))
    (hR : ∀ b, (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ)
          + ((T : ℝ) / 2 - 1 / (2 * δ))
          - (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b))
          ≤ R b) :
    ∃ b : Fin m, (1 / 100 : ℝ) * Real.sqrt ((T : ℝ) * m / δ) ≤ R b := by
  haveI : NeZero m := ⟨by omega⟩
  have hm20 : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hT0 : (0 : ℝ) < T := by nlinarith
  -- `s` is the target scale `√(D' m T)`
  set s : ℝ := Real.sqrt ((T : ℝ) * m / δ) with hsdef
  have hquot : (0 : ℝ) < (T : ℝ) * m / δ := by positivity
  have hs0 : 0 < s := Real.sqrt_pos.mpr hquot
  have hs2 : s ^ 2 = (T : ℝ) * m / δ := Real.sq_sqrt hquot.le
  have hTm : (T : ℝ) * m = δ * s ^ 2 := by rw [hs2]; field_simp
  -- `ε = m / (5 s)`
  have hεs : ε = (m : ℝ) / (5 * s) := by
    have h1 : Real.sqrt (δ * m / T) * s = m := by
      rw [hsdef, ← Real.sqrt_mul (by positivity)]
      have h2 : δ * (m : ℝ) / T * ((T : ℝ) * m / δ) = (m : ℝ) ^ 2 := by
        field_simp
      rw [h2, Real.sqrt_sq hm0.le]
    have h3 : Real.sqrt (δ * (m : ℝ) / T) = (m : ℝ) / s := (eq_div_iff hs0.ne').mpr h1
    rw [hε, h3]; ring
  have hε0 : 0 < ε := by rw [hεs]; positivity
  -- `s ≥ 4m/δ`, the consequence of `16m ≤ δT`
  have hms : 4 * (m : ℝ) / δ ≤ s := by
    have key : (4 * (m : ℝ) / δ) ^ 2 ≤ (T : ℝ) * m / δ := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hδ0]
      nlinarith [mul_nonneg (mul_pos hm0 hδ0).le (sub_nonneg.mpr hT)]
    calc 4 * (m : ℝ) / δ = Real.sqrt ((4 * (m : ℝ) / δ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ s := Real.sqrt_le_sqrt key
  have hmδs : 4 * (m : ℝ) ≤ s * δ := (div_le_iff₀ hδ0).mp hms
  clear_value s
  clear hsdef hquot hs2 hε
  have hδs : 80 ≤ δ * s := by nlinarith
  have hε20 : ε ≤ δ / 20 := by
    rw [hεs, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hεδ : ε ≤ δ := by linarith
  -- the two aggregate quantities
  set SV : ℝ := ∑ b, V b with hSVdef
  set SQ : ℝ := ∑ b, Real.sqrt (2 * V b) with hSQdef
  have hSV0 : 0 ≤ SV := Finset.sum_nonneg fun b _ ↦ hV0 b
  have hSQ0 : 0 ≤ SQ := Finset.sum_nonneg fun b _ ↦ Real.sqrt_nonneg _
  -- Cauchy-Schwarz (Jensen for the square root)
  have hCS : SQ ^ 2 ≤ (m : ℝ) * (2 * SV) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun b ↦ Real.sqrt (2 * V b))
    have h2 : ∀ b : Fin m, Real.sqrt (2 * V b) ^ 2 = 2 * V b := fun b ↦
      Real.sq_sqrt (by linarith [hV0 b])
    simp only [h2, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum] at h
    simpa [hSQdef, hSVdef] using h
  have hu : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
  have hu0 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hSQb : SQ ≤ 41 / 40 * s * Real.sqrt δ := by
    have hrhs0 : (0 : ℝ) ≤ 41 / 40 * s * Real.sqrt δ := by positivity
    have hmd : (m : ℝ) / δ ≤ s / 4 := by
      rw [div_le_div_iff₀ hδ0 (by norm_num)]; linarith
    have hsq : SQ ^ 2 ≤ (41 / 40 * s * Real.sqrt δ) ^ 2 := by
      have h2 : (m : ℝ) * (2 * SV) ≤ (T : ℝ) * m + (m : ℝ) / δ := by
        have := mul_le_mul_of_nonneg_left
          (show 2 * SV ≤ 2 * ((T : ℝ) / 2 + 1 / (2 * δ)) by linarith) hm0.le
        have hid : (m : ℝ) * (2 * ((T : ℝ) / 2 + 1 / (2 * δ))) = (T : ℝ) * m + (m : ℝ) / δ := by
          field_simp
        linarith [hid ▸ this]
      have h3 : (41 / 40 * s * Real.sqrt δ) ^ 2 = 1681 / 1600 * s ^ 2 * δ := by
        rw [mul_pow, mul_pow, hu]; ring
      rw [h3]
      have h4 : (T : ℝ) * m + (m : ℝ) / δ ≤ δ * s ^ 2 + s / 4 := by
        rw [hTm]; linarith
      have h5 : δ * s ^ 2 + s / 4 ≤ 1681 / 1600 * s ^ 2 * δ := by
        nlinarith [mul_pos hs0 hs0]
      linarith
    calc SQ = Real.sqrt (SQ ^ 2) := (Real.sqrt_sq hSQ0).symm
      _ ≤ Real.sqrt ((41 / 40 * s * Real.sqrt δ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 41 / 40 * s * Real.sqrt δ := Real.sqrt_sq hrhs0
  -- sum the per-planting hypothesis
  have hden : (0 : ℝ) < 2 * δ + ε := by linarith
  have hexp : ∑ b : Fin m, ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ)
        + ((T : ℝ) / 2 - 1 / (2 * δ))
        - (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b)))
      = (m : ℝ) * ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ)))
        - ((ε / δ) * SV + (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * SQ) := by
    have hpt : ∀ b : Fin m, (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ)
        + ((T : ℝ) / 2 - 1 / (2 * δ))
        - (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b))
        = ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ)))
          - ((ε / δ) * V b
              + ((ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ))) * Real.sqrt (2 * V b)) := by
      intro b; ring
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum : (m : ℝ) * ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ)
        + ((T : ℝ) / 2 - 1 / (2 * δ)))
      - ((ε / δ) * SV + (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * SQ)
      ≤ ∑ b, R b := by
    rw [← hexp]
    exact Finset.sum_le_sum fun b _ ↦ hR b
  -- the three estimates
  have hTe : (T : ℝ) * ε = δ * s / 5 := by
    rw [hεs, mul_div_assoc']
    rw [div_eq_div_iff (by positivity) (by norm_num : (5 : ℝ) ≠ 0)]
    linear_combination 5 * hTm
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hdne : 2 * δ + ε ≠ 0 := ne_of_gt hden
  have hA : (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ))
      = (T : ℝ) * ε / (2 * (2 * δ + ε)) - 1 / (2 * δ) := by
    field_simp
    ring
  have hlead : 2 * s / 41 ≤ (T : ℝ) * ε / (2 * (2 * δ + ε)) := by
    have hb : (0 : ℝ) < 2 * (2 * δ + ε) := by linarith
    have hc : 2 * (2 * δ + ε) ≤ 41 * δ / 10 := by linarith
    have h1 : (T : ℝ) * ε / (41 * δ / 10) ≤ (T : ℝ) * ε / (2 * (2 * δ + ε)) :=
      div_le_div_of_nonneg_left (by positivity) hb hc
    have h2 : (T : ℝ) * ε / (41 * δ / 10) = 2 * s / 41 := by
      rw [hTe]; field_simp; ring
    linarith
  have hmid : (m : ℝ) / (2 * δ) ≤ s / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hSVterm : (ε / δ) * SV ≤ s / 10 + s / 3200 := by
    have h1 : (ε / δ) * SV ≤ (ε / δ) * ((T : ℝ) / 2 + 1 / (2 * δ)) :=
      mul_le_mul_of_nonneg_left hVsum (by positivity)
    have h2 : (ε / δ) * ((T : ℝ) / 2 + 1 / (2 * δ))
        = (T : ℝ) * ε / (2 * δ) + ε / (2 * δ ^ 2) := by field_simp
    have h3 : (T : ℝ) * ε / (2 * δ) = s / 10 := by rw [hTe]; field_simp; ring
    have hinv : 1 / δ ≤ s / 80 := by
      rw [div_le_div_iff₀ hδ0 (by norm_num)]; nlinarith
    have h4 : ε / (2 * δ ^ 2) ≤ s / 3200 := by
      calc ε / (2 * δ ^ 2) ≤ (δ / 20) / (2 * δ ^ 2) := by gcongr
        _ = 1 / 40 * (1 / δ) := by field_simp; ring
        _ ≤ 1 / 40 * (s / 80) := by gcongr
        _ = s / 3200 := by ring
    linarith
  have hsne : s ≠ 0 := ne_of_gt hs0
  have huN : Real.sqrt δ ≠ 0 := ne_of_gt hu0
  have hSQterm : (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * SQ ≤ 41 * (m : ℝ) * s / 2000 := by
    have hcoef : (0 : ℝ) ≤ (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) := by positivity
    have h1 : (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * SQ
        ≤ (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * (41 / 40 * s * Real.sqrt δ) :=
      mul_le_mul_of_nonneg_left hSQb hcoef
    have hcancel : (ε / Real.sqrt δ) * Real.sqrt δ = ε := div_mul_cancel₀ ε huN
    have h2 : (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * (41 / 40 * s * Real.sqrt δ)
        = 41 * s / 80 * ((T : ℝ) * ε) * ε / δ := by
      have hre : (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * (41 / 40 * s * Real.sqrt δ)
          = 41 * s / 80 * (T : ℝ) * (ε / δ) * ((ε / Real.sqrt δ) * Real.sqrt δ) := by ring
      rw [hre, hcancel]
      ring
    have h3 : 41 * s / 80 * ((T : ℝ) * ε) * ε / δ = 41 * (m : ℝ) * s / 2000 := by
      rw [hTe, hεs]
      field_simp
      ring
    linarith
  -- assemble
  have hfinal : (m : ℝ) * ((1 / 100 : ℝ) * s)
      ≤ (m : ℝ) * ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ)))
        - ((ε / δ) * SV + (ε / δ) * ((T : ℝ) / 2 * (ε / Real.sqrt δ)) * SQ) := by
    have hAge : 2 * s / 41 - 1 / (2 * δ)
        ≤ (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ)) := by
      rw [hA]; linarith
    have hmul : (m : ℝ) * (2 * s / 41 - 1 / (2 * δ))
        ≤ (m : ℝ) * ((T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ))) :=
      mul_le_mul_of_nonneg_left hAge hm0.le
    have hms20 : 20 * s ≤ (m : ℝ) * s := mul_le_mul_of_nonneg_right hm20 hs0.le
    have hexpand : (m : ℝ) * (2 * s / 41 - 1 / (2 * δ))
        = 2 * ((m : ℝ) * s) / 41 - (m : ℝ) / (2 * δ) := by ring
    linarith only [hmul, hexpand, hmid, hSVterm, hSQterm, hms20, hs0]
  -- extract a planting attaining the average
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ b, R b < (m : ℝ) * ((1 / 100 : ℝ) * s) := by
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
    calc ∑ b, R b < ∑ _b : Fin m, (1 / 100 : ℝ) * s :=
          Finset.sum_lt_sum_of_nonempty hne fun b _ ↦ hcon b
      _ = (m : ℝ) * ((1 / 100 : ℝ) * s) := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  linarith
