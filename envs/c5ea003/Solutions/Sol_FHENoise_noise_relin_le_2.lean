-- Prove2me | solution 2 for FHENoise.noise_relin_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:38.739972+00:00
-- url     : https://prove2.me/submissions/e82da9fb-4db4-4d5e-a2ff-de7adc9ca66d

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R]

variable (G : NoiseGauge R)

namespace FHENoise.NoiseGauge

lemma gamma_pos : 0 < G.gamma := lt_of_lt_of_le zero_lt_one G.gamma_one_le

lemma gamma_nonneg : 0 ≤ G.gamma := le_of_lt G.gamma_pos

lemma nu_le_of_sub (x y : R) : G.nu x ≤ G.nu y + G.nu (x - y) := by
  have h : G.nu (y + (x - y)) ≤ G.nu y + G.nu (x - y) := G.nu_add_le _ _
  simpa using h

lemma gamma_nu_mul_le (x y : R) :
    G.gamma * G.nu (x * y) ≤ (G.gamma * G.nu x) * (G.gamma * G.nu y) := by
  have h := G.nu_mul_le x y
  have hg := G.gamma_nonneg
  nlinarith [G.nu_nonneg x, G.nu_nonneg y, G.gamma_pos]

lemma nu_mul_le_bounds {x y : R} {a b : ℝ} (hx : G.nu x ≤ a) (hy : G.nu y ≤ b) :
    G.nu (x * y) ≤ G.gamma * a * b := by
  have hx0 := G.nu_nonneg x
  have hy0 := G.nu_nonneg y
  have ha : 0 ≤ a := le_trans hx0 hx
  calc G.nu (x * y) ≤ G.gamma * G.nu x * G.nu y := G.nu_mul_le x y
    _ ≤ G.gamma * a * G.nu y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx G.gamma_nonneg) hy0
    _ ≤ G.gamma * a * b := mul_le_mul_of_nonneg_left hy (mul_nonneg G.gamma_nonneg ha)

end FHENoise.NoiseGauge

theorem solution {D : ℝ} (s : R) (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (c : Cipher R) :
    noise G s (relin c) ≤ noise G s c + D := by
  simp only [noise]
  exact le_trans (G.nu_le_of_sub _ _) (by linarith [hrelin c])
