-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.steepShare_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:00:08.644781+00:00
-- url     : https://prove2.me/submissions/755d4d2c-d219-490d-856f-b0198053f073

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {k j : ℕ}
    (hk : 1 ≤ k) (hkj : k < j) : steepShare w a b j < steepShare w a b k := by
  have hrepr : ∀ k : ℕ, 1 ≤ k → steepShare w a b k = w / ((1 - w) * (k : ℝ) ^ (b - a) + w) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hb' : (0 : ℝ) < (k : ℝ) ^ (-b) := Real.rpow_pos_of_pos hkpos _
    have hd' : (0 : ℝ) < (k : ℝ) ^ (b - a) := Real.rpow_pos_of_pos hkpos _
    have h1 : (k : ℝ) ^ (-a) = (k : ℝ) ^ (b - a) * (k : ℝ) ^ (-b) := by
      rw [← Real.rpow_add hkpos]
      congr 1
      ring
    have hD1 : 0 < (1 - w) * ((k : ℝ) ^ (b - a) * (k : ℝ) ^ (-b)) + w * (k : ℝ) ^ (-b) := by
      have := mul_pos (sub_pos.2 hw1) (mul_pos hd' hb')
      have := mul_pos hw0 hb'
      linarith
    have hD2 : 0 < (1 - w) * (k : ℝ) ^ (b - a) + w := by
      have := mul_pos (sub_pos.2 hw1) hd'
      linarith
    unfold steepShare mix pw
    rw [h1, div_eq_div_iff hD1.ne' hD2.ne']
    ring
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkj' : (k : ℝ) < j := by exact_mod_cast hkj
  have hlt : (k : ℝ) ^ (b - a) < (j : ℝ) ^ (b - a) :=
    Real.rpow_lt_rpow hkpos.le hkj' (by linarith)
  have hk' : 0 < (k : ℝ) ^ (b - a) := Real.rpow_pos_of_pos hkpos _
  have hj' : 0 < (j : ℝ) ^ (b - a) := lt_trans hk' hlt
  have hDk : 0 < (1 - w) * (k : ℝ) ^ (b - a) + w := by
    have := mul_pos (sub_pos.2 hw1) hk'
    linarith
  have hDj : 0 < (1 - w) * (j : ℝ) ^ (b - a) + w := by
    have := mul_pos (sub_pos.2 hw1) hj'
    linarith
  rw [hrepr j (by omega), hrepr k hk, div_lt_div_iff₀ hDj hDk]
  have := mul_lt_mul_of_pos_left hlt (sub_pos.2 hw1)
  nlinarith
