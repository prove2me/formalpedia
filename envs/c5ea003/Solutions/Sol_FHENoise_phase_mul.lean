-- Prove2me | solution 1 for FHENoise.phase_mul
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:40.596117+00:00
-- url     : https://prove2.me/submissions/a1b1e36f-a129-4794-99dd-36a30cf50492

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R]

theorem solution (s : R) (c d : Cipher R) :
    phase s (c * d) = phase s c * phase s d := by
  simp [phase]
