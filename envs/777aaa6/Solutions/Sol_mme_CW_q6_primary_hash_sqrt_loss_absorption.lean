-- Prove2me | solution 1 for mme_CW_q6_primary_hash_sqrt_loss_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:06:44.330572+00:00
-- url     : https://prove2.me/submissions/4b2b520f-ea08-4e30-a97b-06a94bfff9c2

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology

theorem solution
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      Real.exp (-((N : ℝ) * loss / 12)) ≤
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ∧
      Real.exp (-((N : ℝ) * loss / 8)) ≤
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  by_cases hCzero : C = 0
  · subst C
    filter_upwards [] with N
    dsimp only
    constructor
    · simp only [zero_mul, neg_zero, Real.exp_zero]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
    · simp only [zero_mul, neg_zero, Real.exp_zero]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ,
        max 1 ((24 * C) ^ 4) ≤ (n₀ : ℝ) :=
      exists_nat_ge (max 1 ((24 * C) ^ 4))
    filter_upwards [eventually_ge_atTop n₀] with N hN
    dsimp only
    have hn₀one : (1 : ℝ) ≤ (n₀ : ℝ) :=
      le_trans (le_max_left _ _) hn₀
    have hNone : 1 ≤ N := by
      have hn₀oneNat : 1 ≤ n₀ := by exact_mod_cast hn₀one
      exact hn₀oneNat.trans hN
    have hpow : (24 * C) ^ 4 ≤ (((N + 1 : ℕ) : ℝ)) := by
      have hn₀pow : (24 * C) ^ 4 ≤ (n₀ : ℝ) :=
        le_trans (le_max_right _ _) hn₀
      have hn₀N : (n₀ : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hN
      push_cast
      linarith
    have h24C : 0 < 24 * C := by positivity
    have h24Csq : 0 < (24 * C) ^ 2 := by positivity
    have hroot : 24 * C ≤
        Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      apply (Real.le_sqrt' h24C).2
      apply (Real.le_sqrt' h24Csq).2
      nlinarith
    let r : ℝ := Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ)))
    let s : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
    have hxnonneg : 0 ≤ (((N + 1 : ℕ) : ℝ)) := by positivity
    have hsnonneg : 0 ≤ s := by
      exact Real.sqrt_nonneg _
    have hrpos : 0 < r := by
      dsimp only [r, s]
      positivity
    have hrsq : r ^ 2 = s := by
      dsimp only [r, s]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have hssq : s ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
      dsimp only [s]
      exact Real.sq_sqrt hxnonneg
    have hxle : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
      push_cast
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    have hscaled : 12 * C * s * r ≤ (N : ℝ) := by
      have hr3nonneg : 0 ≤ r ^ 3 := by positivity
      have hm := mul_le_mul_of_nonneg_right
        (show 24 * C ≤ r by simpa only [r] using hroot) hr3nonneg
      calc
        12 * C * s * r = (12 * C) * r ^ 3 := by
          rw [← hrsq]
          ring
        _ ≤ (r ^ 4) / 2 := by nlinarith
        _ = (((N + 1 : ℕ) : ℝ)) / 2 := by
          nlinarith [hrsq, hssq]
        _ ≤ (N : ℝ) := by linarith
    have hmain12 : C * s ≤ (N : ℝ) * r⁻¹ / 12 := by
      rw [div_eq_mul_inv]
      have h12 : (0 : ℝ) < 12 := by norm_num
      apply (le_mul_inv_iff₀ h12).2
      rw [mul_assoc]
      apply (le_mul_inv_iff₀ hrpos).2
      nlinarith
    have hmain8 : C * s ≤ (N : ℝ) * r⁻¹ / 8 := by
      have hnum : 0 ≤ (N : ℝ) * r⁻¹ := by positivity
      calc
        C * s ≤ (N : ℝ) * r⁻¹ / 12 := hmain12
        _ ≤ (N : ℝ) * r⁻¹ / 8 := by linarith
    constructor
    · apply Real.exp_le_exp.mpr
      dsimp only [r, s] at hmain12 ⊢
      linarith
    · apply Real.exp_le_exp.mpr
      dsimp only [r, s] at hmain8 ⊢
      linarith
