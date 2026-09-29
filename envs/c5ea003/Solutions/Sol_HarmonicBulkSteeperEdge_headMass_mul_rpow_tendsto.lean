-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_mul_rpow_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:25:36.42734+00:00
-- url     : https://prove2.me/submissions/b6d10ba2-66da-4fc0-a4b1-d95a90eb016d

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter Topology HarmonicBulkSteeperEdge in
theorem solution {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (m : ℕ) :
    Tendsto (fun n : ℕ => headMass a n m * (n : ℝ) ^ (1 - a)) atTop
      (𝓝 ((1 - a) * headSum a m)) := by
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
  have h2 : Tendsto (fun n : ℕ => headSum a m / (headSum a n / (n : ℝ) ^ (1 - a))) atTop
      (𝓝 (headSum a m / (1 / (1 - a)))) :=
    tendsto_const_nhds.div hkey (one_div_pos.2 hd).ne'
  rw [div_div_eq_mul_div, div_one, mul_comm] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold headMass
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]
