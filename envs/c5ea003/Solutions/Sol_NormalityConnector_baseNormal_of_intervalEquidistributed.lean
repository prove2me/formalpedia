-- Prove2me | solution 1 for NormalityConnector.baseNormal_of_intervalEquidistributed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:36:48.024247+00:00
-- url     : https://prove2.me/submissions/22f20533-2a90-414a-8455-ce53723ed599

import Mathlib
import Definitions.Def_Probability_NormalityConnector

open NormalityConnector Filter Set Topology in
theorem solution {b : ℕ} (hb : 2 ≤ b) (x : ℝ)
    (hEq : IntervalEquidistributed (fun n => Int.fract ((b : ℝ) ^ n * x))) :
    BaseNormal b x := by
  refine ⟨hb, fun k _ A hA => ?_⟩
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hA1 : (A : ℝ) + 1 ≤ (b : ℝ) ^ k := by
    have h1 : A + 1 ≤ b ^ k := hA
    exact_mod_cast h1
  -- the block `A` is read exactly on the cell `[A/b^k, (A+1)/b^k)`
  have h := hEq ((A : ℝ) / (b : ℝ) ^ k) (((A : ℝ) + 1) / (b : ℝ) ^ k) (by positivity)
    (div_lt_div_of_pos_right (by linarith) hbk) (by rw [div_le_one hbk]; exact hA1)
  have e : ((A : ℝ) + 1) / (b : ℝ) ^ k - (A : ℝ) / (b : ℝ) ^ k = 1 / (b : ℝ) ^ k := by
    ring
  rw [e] at h
  have hf : ∀ N, (Finset.range N).filter (fun n => Int.fract ((b : ℝ) ^ n * x) ∈
        Ico ((A : ℝ) / (b : ℝ) ^ k) (((A : ℝ) + 1) / (b : ℝ) ^ k))
      = (Finset.range N).filter (fun n => digitBlock b k x n = (A : ℤ)) := by
    intro N
    apply Finset.filter_congr
    intro n _
    unfold digitBlock
    rw [Int.floor_eq_iff, Set.mem_Ico, div_le_iff₀ hbk, lt_div_iff₀ hbk]
    push_cast
    rfl
  refine h.congr (fun N => ?_)
  unfold empiricalFrequency
  rw [hf N]
