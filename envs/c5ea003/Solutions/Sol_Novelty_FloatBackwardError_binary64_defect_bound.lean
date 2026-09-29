-- Prove2me | solution 1 for Novelty.FloatBackwardError.binary64_defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:59:31.930646+00:00
-- url     : https://prove2.me/submissions/6e35f7c0-2720-40f0-9331-faf2569a3404

import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
open Novelty.FloatBackwardError in
theorem solution {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (2:ℝ) ^ (-53 : ℤ)) :
    gamma u (2 * logisticCoeffs.length) * hornerAbs logisticCoeffs 1 ≤ (2:ℝ) ^ (-46 : ℤ) := by
  -- the absolute Horner sum of `[0, 4, -4]` at `1` is `8`
  have hH : hornerAbs logisticCoeffs 1 = 8 := by
    simp [hornerAbs, hornerR, logisticCoeffs]
    norm_num
  have hlen : 2 * logisticCoeffs.length = 6 := by simp [logisticCoeffs]
  rw [hH, hlen]
  -- `γ_6` is monotone in the unit roundoff; evaluate it exactly at `2^-53`
  have hmono : gamma u 6 ≤ gamma ((2:ℝ) ^ (-53 : ℤ)) 6 := by
    unfold gamma
    have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1 + u) (by linarith : 1 + u ≤ 1 + (2:ℝ) ^ (-53 : ℤ)) 6
    linarith
  have hval : gamma ((2:ℝ) ^ (-53 : ℤ)) 6 * 8 ≤ (2:ℝ) ^ (-46 : ℤ) := by
    unfold gamma
    norm_num
  nlinarith
