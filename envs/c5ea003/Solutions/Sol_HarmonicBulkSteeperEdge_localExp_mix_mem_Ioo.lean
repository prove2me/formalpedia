-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.localExp_mix_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:06:12.345518+00:00
-- url     : https://prove2.me/submissions/546b7622-5bbf-44ca-a180-70baf6df679f

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {k : ℕ}
    (hk : 1 ≤ k) : a < localExp (mix w a b) k ∧ localExp (mix w a b) k < b := by
  have hX : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hX1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  set t : ℝ := Real.log (((k : ℝ) + 1) / (k : ℝ)) with ht
  have htpos : 0 < t := Real.log_pos (by rw [lt_div_iff₀ hX]; linarith)
  have hpow : ∀ c : ℝ, ((k : ℝ) + 1) ^ (-c) = (k : ℝ) ^ (-c) * Real.exp (-c * t) := by
    intro c
    rw [Real.rpow_def_of_pos hX1, Real.rpow_def_of_pos hX, ← Real.exp_add, ht,
      Real.log_div hX1.ne' hX.ne']
    congr 1
    ring
  set p : ℝ := (1 - w) * (k : ℝ) ^ (-a) with hp
  set s : ℝ := w * (k : ℝ) ^ (-b) with hs
  have hppos : 0 < p := mul_pos (by linarith) (Real.rpow_pos_of_pos hX _)
  have hspos : 0 < s := mul_pos hw0 (Real.rpow_pos_of_pos hX _)
  have hmk : mix w a b k = p + s := by
    simp only [mix, pw, hp, hs]
  have hmk1 : mix w a b (k + 1) = p * Real.exp (-a * t) + s * Real.exp (-b * t) := by
    simp only [mix, pw, hp, hs]
    push_cast
    rw [hpow a, hpow b]
    ring
  have hD : 0 < p * Real.exp (-a * t) + s * Real.exp (-b * t) := by
    have := Real.exp_pos (-a * t)
    have := Real.exp_pos (-b * t)
    positivity
  have hloc : localExp (mix w a b) k
      = Real.log ((p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t))) / t := by
    unfold localExp
    rw [hmk, hmk1]
  have hRpos : 0 < (p + s) / (p * Real.exp (-a * t) + s * Real.exp (-b * t)) :=
    div_pos (by linarith) hD
  have e1 : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hlower : a < localExp (mix w a b) k := by
    rw [hloc, lt_div_iff₀ htpos, ← Real.log_exp (a * t)]
    apply Real.log_lt_log (Real.exp_pos _)
    rw [lt_div_iff₀ hD]
    have e2 : Real.exp (a * t) * Real.exp (-b * t) < 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by nlinarith)
    have h1 := mul_lt_mul_of_pos_left e2 hspos
    have h2 : p * (Real.exp (a * t) * Real.exp (-a * t)) = p := by rw [e1, mul_one]
    nlinarith
  have hupperb : localExp (mix w a b) k < b := by
    rw [hloc, div_lt_iff₀ htpos, ← Real.log_exp (b * t)]
    apply Real.log_lt_log hRpos
    rw [div_lt_iff₀ hD]
    have e3 : Real.exp (b * t) * Real.exp (-b * t) = 1 := by
      rw [← Real.exp_add]
      simp
    have e4 : 1 < Real.exp (b * t) * Real.exp (-a * t) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by nlinarith)
    have h1 := mul_lt_mul_of_pos_left e4 hppos
    have h2 : s * (Real.exp (b * t) * Real.exp (-b * t)) = s := by rw [e3, mul_one]
    nlinarith
  exact ⟨hlower, hupperb⟩
