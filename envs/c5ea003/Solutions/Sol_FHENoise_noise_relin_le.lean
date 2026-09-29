-- Prove2me | solution 1 for FHENoise.noise_relin_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:34:45.529919+00:00
-- url     : https://prove2.me/submissions/2cfb1378-0e7c-4f82-a458-7c95d134f918

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R] (G : NoiseGauge R)

theorem solution {D : ℝ} (s : R) (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (c : Cipher R) :
    noise G s (relin c) ≤ noise G s c + D := by
  unfold noise
  have hle := G.nu_add_le (phase s (relin c) - phase s c) (phase s c)
  have hrew : phase s (relin c) - phase s c + phase s c = phase s (relin c) := by
    abel
  rw [← hrew]
  linarith [hrelin c]
