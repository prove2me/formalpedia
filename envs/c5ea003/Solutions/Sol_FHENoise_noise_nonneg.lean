-- Prove2me | solution 1 for FHENoise.noise_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:21.899841+00:00
-- url     : https://prove2.me/submissions/7235153c-a742-4358-8f75-6977d57e5648

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R] (G : NoiseGauge R)

theorem solution (s : R) (c : Cipher R) : 0 ≤ noise G s c :=
  G.nu_nonneg (phase s c)
