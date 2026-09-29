-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_doubling_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:32:54.191576+00:00
-- url     : https://prove2.me/submissions/f3a609d6-b794-4383-90cd-3644ff64e686

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter Topology HarmonicBulkSteeperEdge in
theorem solution {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => headMass a (2 * n) m / headMass a n m) atTop
      (𝓝 ((2 : ℝ) ^ (a - 1))) := by
  have hd : 0 < 1 - a := by linarith
  have hsumR : ∀ n : ℕ, headSum a n = ∑ i ∈ range n, ((1 : ℝ) + i) ^ (-a) := by
    intro n
    unfold headSum pw
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by norm_num
  have hanti : ∀ N : ℕ, AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc 1 (1 + (N : ℝ))) := by
    intro N x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint : ∀ N : ℕ, ∫ x in (1 : ℝ)..(1 + (N : ℝ)), x ^ (-a)
      = ((1 + (N : ℝ)) ^ (1 - a) - 1) / (1 - a) := by
    intro N
    rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow, show -a + 1 = 1 - a by ring]
  have hlow : ∀ n : ℕ, ((1 + (n : ℝ)) ^ (1 - a) - 1) / (1 - a) ≤ headSum a n := by
    intro n
    rw [← hint n, hsumR n]
    exact (hanti n).integral_le_sum
  have hup : ∀ n : ℕ, 1 ≤ n → headSum a n ≤ 1 + ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    intro n hn
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [hsumR, Finset.sum_range_succ']
    have h1 := (hanti N).sum_le_integral
    rw [hint N] at h1
    rw [show ((N + 1 : ℕ) : ℝ) = 1 + N by push_cast; ring]
    simp only [Nat.cast_zero, add_zero, Real.one_rpow]
    linarith
  have hkey : Tendsto (fun n : ℕ => headSum a n / (n : ℝ) ^ (1 - a)) atTop (𝓝 (1 / (1 - a))) := by
    have he : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - a))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
    have hlo : Tendsto (fun n : ℕ => 1 / (1 - a) - 1 / (1 - a) * (n : ℝ) ^ (-(1 - a))) atTop
        (𝓝 (1 / (1 - a))) := by
      simpa using (he.const_mul (1 / (1 - a))).const_sub (1 / (1 - a))
    have hhi : Tendsto (fun n : ℕ => 1 / (1 - a) + (1 - 1 / (1 - a)) * (n : ℝ) ^ (-(1 - a)))
        atTop (𝓝 (1 / (1 - a))) := by
      simpa using (he.const_mul (1 - 1 / (1 - a))).const_add (1 / (1 - a))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hP : 0 < (n : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by linarith) _
      have hinv : (n : ℝ) ^ (-(1 - a)) * (n : ℝ) ^ (1 - a) = 1 := by
        rw [Real.rpow_neg (by linarith), inv_mul_cancel₀ hP.ne']
      have hmono : (n : ℝ) ^ (1 - a) ≤ (1 + (n : ℝ)) ^ (1 - a) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hd.le
      rw [le_div_iff₀ hP]
      have e : (1 / (1 - a) - 1 / (1 - a) * (n : ℝ) ^ (-(1 - a))) * (n : ℝ) ^ (1 - a)
          = ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by
        rw [sub_mul, mul_assoc, hinv]
        ring
      rw [e]
      exact le_trans ((div_le_div_iff_of_pos_right hd).2 (by linarith)) (hlow n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hP : 0 < (n : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by linarith) _
      have hinv : (n : ℝ) ^ (-(1 - a)) * (n : ℝ) ^ (1 - a) = 1 := by
        rw [Real.rpow_neg (by linarith), inv_mul_cancel₀ hP.ne']
      rw [div_le_iff₀ hP]
      have e : (1 / (1 - a) + (1 - 1 / (1 - a)) * (n : ℝ) ^ (-(1 - a))) * (n : ℝ) ^ (1 - a)
          = 1 + ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by
        rw [add_mul, mul_assoc, hinv]
        ring
      rw [e]
      exact hup n hn
  have hpos : ∀ n : ℕ, 1 ≤ n → 0 < headSum a n := by
    intro n hn
    unfold headSum
    exact Finset.sum_pos (fun k hk => Real.rpow_pos_of_pos (by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this) _) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hn⟩⟩
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  have hkey2 := hkey.comp h2n
  have hlim := (hkey.div hkey2 (one_div_pos.2 hd).ne').mul_const ((2 : ℝ) ^ (a - 1))
  rw [div_self (one_div_pos.2 hd).ne', one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hSm := hpos m hm
  have hSn := hpos n hn
  have hS2n := hpos (2 * n) (by omega)
  have hP : 0 < (n : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by linarith) _
  have h2P : ((2 * n : ℕ) : ℝ) ^ (1 - a) = (2 : ℝ) ^ (1 - a) * (n : ℝ) ^ (1 - a) := by
    push_cast
    exact Real.mul_rpow (by norm_num) (by linarith)
  have h2inv : (2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (1 - a) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have h2pos : 0 < (2 : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by norm_num) _
  simp only [Pi.div_apply, Function.comp_apply, h2P]
  unfold headMass
  have hRQ : (2 : ℝ) ^ (1 - a) * (2 : ℝ) ^ (a - 1) = 1 := by
    rw [mul_comm]
    exact h2inv
  have e1 : headSum a n / (n : ℝ) ^ (1 - a)
        / (headSum a (2 * n) / ((2 : ℝ) ^ (1 - a) * (n : ℝ) ^ (1 - a))) * (2 : ℝ) ^ (a - 1)
      = headSum a n * ((2 : ℝ) ^ (1 - a) * (2 : ℝ) ^ (a - 1)) / headSum a (2 * n) := by
    field_simp
    try ring
  rw [e1, hRQ, mul_one]
  field_simp
  try ring
