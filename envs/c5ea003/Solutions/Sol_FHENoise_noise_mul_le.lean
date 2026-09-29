-- Prove2me | solution 1 for FHENoise.noise_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:28:19.390898+00:00
-- url     : https://prove2.me/submissions/e594a722-66f1-4d47-997c-f6d6664fb408

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R] (G : NoiseGauge R)

theorem solution (s : R) (c d : Cipher R) :
    noise G s (c * d) ≤ G.gamma * noise G s c * noise G s d := by
  -- phase is a ring homomorphism, so phase(c*d) = phase(c)*phase(d)
  simpa [noise, phase, Polynomial.eval_mul] using
    G.nu_mul_le (phase s c) (phase s d)
