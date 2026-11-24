-- Prove2me | solution 1 for FHENoise.bootIter_plain
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:29.906986+00:00
-- url     : https://prove2.me/submissions/fbb2f8d4-3528-47a0-a12e-95a9791bf8aa

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE
import Definitions.Def_Cryptography_FHE_Bootstrapping

open FHENoise

variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

namespace FHENoise.NoiseGauge

lemma gamma_pos : 0 < G.gamma := lt_of_lt_of_le zero_lt_one G.gamma_one_le

lemma gamma_nonneg : 0 ≤ G.gamma := le_of_lt G.gamma_pos

lemma nu_le_of_sub (x y : R) : G.nu x ≤ G.nu y + G.nu (x - y) := by
  have h : G.nu (y + (x - y)) ≤ G.nu y + G.nu (x - y) := G.nu_add_le _ _
  simpa using h

end FHENoise.NoiseGauge

@[simp] lemma phase_add (s : R) (c d : Cipher R) :
    phase s (c + d) = phase s c + phase s d := by
  simp [phase]

@[simp] lemma phase_mul (s : R) (c d : Cipher R) :
    phase s (c * d) = phase s c * phase s d := by
  simp [phase]

lemma noise_nonneg (s : R) (c : Cipher R) : 0 ≤ noise G s c := G.nu_nonneg _

theorem noise_mul_le (s : R) (c d : Cipher R) :
    noise G s (c * d) ≤ G.gamma * noise G s c * noise G s d := by
  simpa [noise] using G.nu_mul_le (phase s c) (phase s d)

theorem noise_relin_le {D : ℝ} (s : R) (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (c : Cipher R) :
    noise G s (relin c) ≤ noise G s c + D := by
  simp only [noise]
  exact le_trans (G.nu_le_of_sub _ _) (by linarith [hrelin c])

@[simp] lemma iterD_succ (gamma D x : ℝ) (d : ℕ) :
    iterD gamma D (d + 1) x = noiseStep gamma D (iterD gamma D d x) := rfl

theorem noise_sqBlock_le {D x : ℝ} (G : NoiseGauge R) (s : R)
    (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
    (c : Cipher R) (hc : noise G s c ≤ x) (hx : 0 ≤ x) :
    ∀ n, noise G s (sqBlock relin n c) ≤ iterD G.gamma D n x
  | 0 => hc
  | (n + 1) => by
      have ih := noise_sqBlock_le G s relin hrelin hD c hc hx n
      have h0 := noise_nonneg G s (sqBlock relin n c)
      have hmul := noise_mul_le G s (sqBlock relin n c) (sqBlock relin n c)
      have hrel := noise_relin_le G s relin hrelin (sqBlock relin n c * sqBlock relin n c)
      have hsq := mul_self_le_mul_self h0 ih
      have hg := G.gamma_nonneg
      simp only [sqBlock, sqStep, iterD_succ, noiseStep]
      nlinarith [hsq, hg, hmul, hrel]

theorem plain_sqBlock {M : Type*} [CommRing M] (s : R) (pi : R →+* M)
    (relin : Cipher R → Cipher R)
    (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c)) (c : Cipher R) :
    ∀ n, pi (phase s (sqBlock relin n c)) = (pi (phase s c)) ^ (2 ^ n)
  | 0 => by simp [sqBlock]
  | (n + 1) => by
      have ih := plain_sqBlock s pi relin hrelinP c n
      have hstep : pi (phase s (sqStep relin (sqBlock relin n c)))
          = pi (phase s (sqBlock relin n c)) * pi (phase s (sqBlock relin n c)) := by
        rw [sqStep, hrelinP, phase_mul, map_mul]
      rw [sqBlock, hstep, ih, ← pow_add, pow_succ]
      ring_nf

theorem bootIter_noise_le {D T Bref : ℝ} (G : NoiseGauge R) (s : R)
    (relin refresh : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
    (hrefN : ∀ c, noise G s c < T → noise G s (refresh c) ≤ Bref)
    (hBref : 0 ≤ Bref) (L : ℕ) (hsafe : iterD G.gamma D L Bref < T)
    (c : Cipher R) (hc : noise G s c ≤ Bref) :
    ∀ k, noise G s (bootIter relin refresh L k c) ≤ Bref
  | 0 => hc
  | (k + 1) => by
      have ih := bootIter_noise_le G s relin refresh hrelin hD hrefN hBref L hsafe c hc k
      have hblock := noise_sqBlock_le G s relin hrelin hD
        (bootIter relin refresh L k c) ih hBref L
      exact hrefN _ (lt_of_le_of_lt hblock hsafe)

theorem solution {M : Type*} [CommRing M] {D T Bref : ℝ} (G : NoiseGauge R) (s : R)
    (pi : R →+* M) (relin refresh : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
    (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c))
    (hrefN : ∀ c, noise G s c < T → noise G s (refresh c) ≤ Bref)
    (hrefP : ∀ c, noise G s c < T → pi (phase s (refresh c)) = pi (phase s c))
    (hBref : 0 ≤ Bref) (L : ℕ) (hsafe : iterD G.gamma D L Bref < T)
    (c : Cipher R) (hc : noise G s c ≤ Bref) :
    ∀ k, pi (phase s (bootIter relin refresh L k c)) = (pi (phase s c)) ^ (2 ^ (L * k))
  | 0 => by simp [bootIter]
  | (k + 1) => by
      have ih := solution G s pi relin refresh hrelin hD hrelinP hrefN hrefP hBref
        L hsafe c hc k
      have hnk := bootIter_noise_le G s relin refresh hrelin hD hrefN hBref L hsafe c hc k
      have hblock := noise_sqBlock_le G s relin hrelin hD
        (bootIter relin refresh L k c) hnk hBref L
      have hlt : noise G s (sqBlock relin L (bootIter relin refresh L k c)) < T :=
        lt_of_le_of_lt hblock hsafe
      have hplain := plain_sqBlock s pi relin hrelinP (bootIter relin refresh L k c) L
      have hexp : 2 ^ (L * k) * 2 ^ L = 2 ^ (L * (k + 1)) := by
        rw [← pow_add]
        ring_nf
      rw [bootIter, hrefP _ hlt, hplain, ih, ← pow_mul, hexp]
