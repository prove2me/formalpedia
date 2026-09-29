-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.steepShare_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:10:54.376423+00:00
-- url     : https://prove2.me/submissions/868f49ca-185c-4714-a8a1-444b82d0fffc

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) :
    Tendsto (fun k : ℕ => steepShare w a b k) atTop (nhds 0) := by
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
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun k : ℕ => (1 - w) * (k : ℝ) ^ (b - a) + w) atTop atTop :=
    tendsto_atTop_add_const_right _ w (h1.const_mul_atTop (by linarith))
  have h3 : Tendsto (fun k : ℕ => w / ((1 - w) * (k : ℝ) ^ (b - a) + w)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (hrepr k hk).symm
