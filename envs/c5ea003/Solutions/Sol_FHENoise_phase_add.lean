-- Prove2me | solution 1 for FHENoise.phase_add
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:37.037015+00:00
-- url     : https://prove2.me/submissions/c6fee656-cff9-485f-a250-73fbba87786c

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R]

theorem solution (s : R) (c d : Cipher R) :
    phase s (c + d) = phase s c + phase s d := by
  simp [phase]
