-- Prove2me | solution 1 for FHENoise.iterD_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:26.772695+00:00
-- url     : https://prove2.me/submissions/6f8e94e5-8b6d-4ad7-aae7-6eb4078c35b6

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseDichotomy
import Definitions.Def_Cryptography_FHE_NoiseGrowth

open FHENoise

theorem solution {gamma D x : ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D) (hx : 0 ≤ x) :
    ∀ d, 0 ≤ iterD gamma D d x := by
  intro d
  induction d with
  | zero => simpa [iterD] using hx
  | succ d ih =>
      simp only [iterD, noiseStep]
      nlinarith [sq_nonneg (iterD gamma D d x)]
