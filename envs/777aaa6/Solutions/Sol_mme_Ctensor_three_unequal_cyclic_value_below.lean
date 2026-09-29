-- Prove2me | solution 1 for mme_Ctensor_three_unequal_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:44:49.662339+00:00
-- url     : https://prove2.me/submissions/c788b0a1-ff2a-4dd6-8812-75265977f40b

import Theorems.Thm_mme_Ctensor_three_unequal_all_words_min_pair_extraction
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

private theorem min_pow_nat (a b R : ℕ) :
    min (a ^ R) (b ^ R) = (min a b) ^ R := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (Nat.pow_le_pow_left hab R)]
  · rw [min_eq_right hba, min_eq_right (Nat.pow_le_pow_left hba R)]

private theorem pow_add_one_le_succ_pow (H R : ℕ) (hH : 0 < H) :
    H ^ R + 1 ≤ (H + 1) ^ (R + 1) := by
  have hpow : H ^ R ≤ (H + 1) ^ R := Nat.pow_le_pow_left (by omega) R
  have hone : 1 ≤ (H + 1) ^ R := Nat.one_le_pow R (H + 1) (by omega)
  rw [pow_succ]
  nlinarith only [hpow, hone, hH]

private theorem log_min_word_bound (H0 H1 H2 R : ℕ) (hH0 : 0 < H0) :
    Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ)) ≤
      ((R + 1 : ℕ) : ℝ) * Real.log ((H0 + 1 : ℕ) : ℝ) := by
  have hn : min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 ≤
      (H0 + 1) ^ (R + 1) :=
    (Nat.add_le_add_right (min_le_left _ _) 1).trans
      (pow_add_one_le_succ_pow H0 R hH0)
  have hlog := Real.log_le_log (by positivity :
      (0 : ℝ) < ((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ))
    (show (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ)) ≤
        (((H0 + 1) ^ (R + 1) : ℕ) : ℝ) by exact_mod_cast hn)
  simpa only [Nat.cast_pow, Real.log_pow] using hlog

private theorem finite_loss_dominated (H0 H1 H2 R : ℕ) (hH0 : 0 < H0) :
    Real.exp (-(100 * Real.sqrt (Real.log ((H0 + 1 : ℕ) : ℝ)) + Real.log 2) *
      Real.sqrt ((R + 1 : ℕ) : ℝ)) ≤
      Real.exp (-100 * Real.sqrt
        (Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ)))) / 2 := by
  have hlog := log_min_word_bound H0 H1 H2 R hH0
  have hsqrt := Real.sqrt_le_sqrt hlog
  rw [Real.sqrt_mul (by positivity)] at hsqrt
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((R + 1 : ℕ) : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Nat.le_add_left 1 R)
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have harg :
      -(100 * Real.sqrt (Real.log ((H0 + 1 : ℕ) : ℝ)) + Real.log 2) *
          Real.sqrt ((R + 1 : ℕ) : ℝ) ≤
        -100 * Real.sqrt
          (Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ))) -
          Real.log 2 := by
    nlinarith only [hsqrt, mul_le_mul_of_nonneg_left hs1 hlog2]
  have hexp := Real.exp_le_exp.mpr harg
  simpa only [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp


open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2)
    (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < ((min (H0 * H1) (min (H0 * H2) (H1 * H2)) : ℕ) : ℝ) *
      (((v0 * v1 * v2 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (threeStarCyclicProduct X Y Z) tau V := by
  let M : ℕ := min (H0 * H1) (min (H0 * H2) (H1 * H2))
  let W : ℝ := ((v0 * v1 * v2 : ℕ) : ℝ) ^ tau
  let B : ℝ := (M : ℝ) * W
  let C : ℝ := 100 * Real.sqrt (Real.log ((H0 + 1 : ℕ) : ℝ)) + Real.log 2
  have hvolume : (0 : ℝ) < ((v0 * v1 * v2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hv0 hv1) hv2
  have hW : 0 ≤ W := (Real.rpow_pos_of_pos hvolume tau).le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.log_nonneg (by norm_num))
  have hgap := mme_strict_pow_absorbs_sqrt_exp_loss V B C hV hVlt hC
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (threeStarCyclicProduct X Y Z) tau V hV id tendsto_id
    (fun _ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hgap] with R hR
  obtain ⟨k, a, b, c, hrestrict, hcount, hvol⟩ :=
    mme_Ctensor_three_unequal_all_words_min_pair_extraction certX certY certZ h0 h1 h2 R
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simp only [id_eq, sub_zero, mul_one]
  have hsum :
      (∑ i : Fin k, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) = (k : ℝ) * W ^ R := by
    simp_rw [hvol, Nat.cast_pow, ← Real.rpow_pow_comm hvolume.le tau R]
    simp [W]
  simp only [min_pow_nat, Nat.cast_pow] at hcount
  have hweight : 0 ≤ (M : ℝ) ^ R * W ^ R :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hW _)
  calc
    V ^ R ≤ B ^ R * Real.exp (-C * Real.sqrt ((R + 1 : ℕ) : ℝ)) := hR
    _ = ((M : ℝ) ^ R * W ^ R) *
        Real.exp (-C * Real.sqrt ((R + 1 : ℕ) : ℝ)) := by rw [show B = (M : ℝ) * W from rfl, mul_pow]
    _ ≤ (((M : ℝ) ^ R / 2) * Real.exp (-100 * Real.sqrt
        (Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ))))) * W ^ R := by
      have hh := mul_le_mul_of_nonneg_left (finite_loss_dominated H0 H1 H2 R h0) hweight
      dsimp [C]
      convert hh using 1
      ring
    _ ≤ (k : ℝ) * W ^ R :=
      mul_le_mul_of_nonneg_right (by simpa only [M, min_pow_nat] using hcount)
        (pow_nonneg hW R)
    _ = ∑ i : Fin k, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := hsum.symm
