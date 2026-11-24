-- Prove2me | solution 1 for FHENoise.NoiseCkt.noise_evalEnc_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:35.247758+00:00
-- url     : https://prove2.me/submissions/b16a7599-2f02-4f49-8e78-dd80a333fe45

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise
open FHENoise.NoiseCkt

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

@[simp] lemma phase_add (s : R) (c d : Cipher R) :
    phase s (c + d) = phase s c + phase s d := by
  simp [phase]

@[simp] lemma phase_mul (s : R) (c d : Cipher R) :
    phase s (c * d) = phase s c * phase s d := by
  simp [phase]

lemma noise_nonneg (s : R) (c : Cipher R) : 0 ≤ noise G s c := G.nu_nonneg _

theorem noise_add_le (s : R) (c d : Cipher R) :
    noise G s (c + d) ≤ noise G s c + noise G s d := by
  simpa [noise] using G.nu_add_le (phase s c) (phase s d)

theorem noise_mul_le (s : R) (c d : Cipher R) :
    noise G s (c * d) ≤ G.gamma * noise G s c * noise G s d := by
  simpa [noise] using G.nu_mul_le (phase s c) (phase s d)

theorem noise_relin_le {D : ℝ} (s : R) (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (c : Cipher R) :
    noise G s (relin c) ≤ noise G s c + D := by
  simp only [noise]
  exact le_trans (G.nu_le_of_sub _ _) (by linarith [hrelin c])

lemma noiseBound_nonneg {gamma D : ℝ} {beta : ℕ → ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D)
    (hbeta : ∀ i, 0 ≤ beta i) : ∀ f : NoiseCkt, 0 ≤ f.noiseBound gamma D beta
  | .leaf i => hbeta i
  | .add f g => by
      have := noiseBound_nonneg hg hD hbeta f
      have := noiseBound_nonneg hg hD hbeta g
      simp only [noiseBound]; linarith
  | .mul f g => by
      have h1 := noiseBound_nonneg hg hD hbeta f
      have h2 := noiseBound_nonneg hg hD hbeta g
      have : 0 ≤ gamma * f.noiseBound gamma D beta * g.noiseBound gamma D beta :=
        mul_nonneg (mul_nonneg hg h1) h2
      simp only [noiseBound]; linarith

theorem solution {D : ℝ} (G : NoiseGauge R) (s : R)
    (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D)
    (rho : ℕ → Cipher R) (beta : ℕ → ℝ) (hleaf : ∀ i, noise G s (rho i) ≤ beta i) :
    ∀ f : NoiseCkt, noise G s (f.evalEnc relin rho) ≤ f.noiseBound G.gamma D beta
  | .leaf i => hleaf i
  | .add f g => by
      have h1 := solution G s relin hrelin rho beta hleaf f
      have h2 := solution G s relin hrelin rho beta hleaf g
      have := noise_add_le G s (f.evalEnc relin rho) (g.evalEnc relin rho)
      simp only [evalEnc, noiseBound]
      linarith
  | .mul f g => by
      have h1 := solution G s relin hrelin rho beta hleaf f
      have h2 := solution G s relin hrelin rho beta hleaf g
      have hprod := noise_mul_le G s (f.evalEnc relin rho) (g.evalEnc relin rho)
      have hrel := noise_relin_le G s relin hrelin
        (f.evalEnc relin rho * g.evalEnc relin rho)
      have n1 := noise_nonneg G s (f.evalEnc relin rho)
      have n2 := noise_nonneg G s (g.evalEnc relin rho)
      have hg := G.gamma_nonneg
      have hbf := noiseBound_nonneg hg (le_trans (G.nu_nonneg _) (hrelin 0))
        (fun i => le_trans (noise_nonneg G s (rho i)) (hleaf i)) f
      have hmm := mul_le_mul h1 h2 n2 hbf
      simp only [evalEnc, noiseBound]
      nlinarith [hmm, hg, hprod, hrel]
