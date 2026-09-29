-- Prove2me | solution 1 for mme_MM_induced_matching_quarter_root_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:42:27.546632+00:00
-- url     : https://prove2.me/submissions/ab6d942e-f32a-41f0-b61e-d19fc5ab6b60

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

open Filter Topology

theorem solution :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      ∀ H : ℕ, 0 < H → H ≤ 4 ^ N →
        ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤
          ((H : ℝ) ^ 2) *
            Real.exp (-100 *
              Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
  filter_upwards [eventually_ge_atTop (800 ^ 4)] with N hN
  dsimp only
  intro H hH hHbound
  have hNlarge : ((800 : ℝ) ^ 4) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNp1 : 0 ≤ (N : ℝ) + 1 := by positivity
  have hsqrtN :
      Real.sqrt ((N : ℝ) + 1) ≤ 2 * Real.sqrt (N : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hNr]
  have hsqrtSqrtN :
      Real.sqrt (Real.sqrt ((N : ℝ) + 1)) ≤
        2 * Real.sqrt (Real.sqrt (N : ℝ)) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (N : ℝ))]
  have h800 : (800 : ℝ) ≤ Real.sqrt (Real.sqrt (N : ℝ)) := by
    apply (Real.le_sqrt' (by norm_num : (0 : ℝ) < 800)).2
    apply (Real.le_sqrt' (by positivity :
      (0 : ℝ) < (800 : ℝ) ^ 2)).2
    nlinarith
  have hdenomPos :
      0 < Real.sqrt (Real.sqrt ((N : ℝ) + 1)) := by
    positivity
  have hrootBudget :
      200 * Real.sqrt ((N : ℝ) + 1) ≤
        (N : ℝ) /
          Real.sqrt (Real.sqrt ((N : ℝ) + 1)) := by
    apply (le_div_iff₀ hdenomPos).2
    calc
      200 * Real.sqrt ((N : ℝ) + 1) *
            Real.sqrt (Real.sqrt ((N : ℝ) + 1))
          ≤ 200 * (2 * Real.sqrt (N : ℝ)) *
              (2 * Real.sqrt (Real.sqrt (N : ℝ))) := by
            gcongr
      _ = 800 * Real.sqrt (N : ℝ) *
            Real.sqrt (Real.sqrt (N : ℝ)) := by ring
      _ ≤ Real.sqrt (Real.sqrt (N : ℝ)) *
            Real.sqrt (N : ℝ) *
            Real.sqrt (Real.sqrt (N : ℝ)) := by
            gcongr
      _ = (N : ℝ) := by
            nlinarith [Real.sq_sqrt hNr,
              Real.sq_sqrt (Real.sqrt_nonneg (N : ℝ))]
  have hHcast : ((H + 1 : ℕ) : ℝ) ≤
      2 * ((4 : ℝ) ^ N) := by
    have hone_le : (1 : ℕ) ≤ 4 ^ N := by
      have : 0 < 4 ^ N := pow_pos (by omega) N
      omega
    have : H + 1 ≤ 2 * 4 ^ N := by omega
    exact_mod_cast this
  have hlogUpper :
      Real.log (((H + 1 : ℕ) : ℝ)) ≤
        4 * ((N : ℝ) + 1) := by
    have hlogMono :=
      Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
        hHcast
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num :
        (0 : ℝ) < 2)]
    have hlogFour : Real.log (4 : ℝ) ≤ 3 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num :
        (0 : ℝ) < 4)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero N (by norm_num : (4 : ℝ) ≠ 0)),
      Real.log_pow] at hlogMono
    push_cast at hlogMono
    have hNlog :
        (N : ℝ) * Real.log 4 ≤ (N : ℝ) * 3 :=
      mul_le_mul_of_nonneg_left hlogFour hNr
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hsqrtLog :
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤
        2 * Real.sqrt ((N : ℝ) + 1) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hNp1]
  have hexponent :
      100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤
        (N : ℝ) *
          (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one]
    rw [← div_eq_mul_inv]
    have hscaledLog :
        100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤
          200 * Real.sqrt ((N : ℝ) + 1) :=
      by
        have hscaledLog' :=
          mul_le_mul_of_nonneg_left hsqrtLog
            (by norm_num : (0 : ℝ) ≤ 100)
        nlinarith
    simpa [Nat.cast_add, Nat.cast_one] using hscaledLog.trans hrootBudget
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (H : ℝ))
  apply Real.exp_le_exp.mpr
  nlinarith
