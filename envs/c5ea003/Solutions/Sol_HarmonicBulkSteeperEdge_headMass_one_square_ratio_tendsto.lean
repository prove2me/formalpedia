-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_one_square_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:17:05.98198+00:00
-- url     : https://prove2.me/submissions/65d88307-486b-4ad9-835f-7ee945f53389

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter Topology HarmonicBulkSteeperEdge in
theorem solution {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => headMass 1 (n * n) m / headMass 1 n m) atTop (𝓝 (1/2)) := by
  have hH : ∀ n : ℕ, headSum 1 n = (harmonic n : ℝ) := by
    intro n
    unfold headSum pw
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun k _ => Real.rpow_neg_one _
  have hHpos : ∀ n : ℕ, 1 ≤ n → 0 < headSum 1 n := by
    intro n hn
    unfold headSum
    exact Finset.sum_pos (fun k hk => Real.rpow_pos_of_pos (by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this) _) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hn⟩⟩
  -- `H(n) / log n → 1`
  have hT : Tendsto (fun n : ℕ => headSum 1 n / Real.log n) atTop (𝓝 1) := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hhi : Tendsto (fun n : ℕ => 1 + 1 / Real.log n) atTop (𝓝 1) := by
      have h1 := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop
        hlog).const_add (1 : ℝ)
      simpa using h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 < Real.log n := Real.log_pos (by linarith)
      rw [le_div_iff₀ hl, one_mul, hH]
      have h1 := log_add_one_le_harmonic n
      have h2 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by push_cast; linarith)
      linarith
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 < Real.log n := Real.log_pos (by linarith)
      rw [div_le_iff₀ hl, hH, add_mul, one_div, inv_mul_cancel₀ hl.ne', one_mul]
      have := harmonic_le_one_add_log n
      linarith
  have hsq : Tendsto (fun n : ℕ => n * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => le_trans hn (Nat.le_mul_self n)⟩
  have hT2 := hT.comp hsq
  have hlim := (hT.div hT2 one_ne_zero).mul_const (1 / 2 : ℝ)
  rw [div_one, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have hSm := hHpos m hm
  have hSn := hHpos n (by omega)
  have hSnn := hHpos (n * n) (by nlinarith)
  have hlog2 : Real.log ((n * n : ℕ) : ℝ) = 2 * Real.log n := by
    push_cast
    rw [Real.log_mul (by linarith) (by linarith)]
    ring
  simp only [Pi.div_apply, Function.comp_apply, hlog2]
  unfold headMass
  field_simp
  try ring
