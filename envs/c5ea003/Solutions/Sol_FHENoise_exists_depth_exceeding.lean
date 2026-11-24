-- Prove2me | solution 1 for FHENoise.exists_depth_exceeding
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:07:13.679922+00:00
-- url     : https://prove2.me/submissions/987e1dab-f905-4ccd-a242-bd50515e362b

-- Thm stub generated from Cryptography/FHE/NoiseDichotomy.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseDichotomy
import Definitions.Def_Cryptography_FHE_NoiseGrowth

/-!
# The bootstrapping dichotomy: when is a levelled FHE scheme noise-stable?

Homomorphic multiplication followed by relinearization transforms the
(normalized) noise level `x` by the quadratic map

`noiseStep γ D x = γ · x² + D`,

where `γ ≥ 1` is the ring expansion factor and `D ≥ 0` is the key-switching
noise surcharge.  Everything about unbounded-depth evaluation is governed by the
orbit structure of this one-dimensional quadratic dynamical system, and the
governing quantity is the discriminant `1 - 4γD`.

## Main results

* `noiseStep_dichotomy` — **the dichotomy**: an invariant noise budget exists
  (i.e. `∃ Q ≥ 0, γQ² + D ≤ Q`) **iff** `4γD ≤ 1`.  There is no middle ground.
* `iterD_le_of_invariant` — inside the stable regime the noise never leaves the
  invariant interval, at *any* multiplicative depth: no bootstrapping needed.
* `noiseFixedPoint_spec` — the explicit stable budget
  `Q = (1 - √(1 - 4γD)) / (2γ)`, an exact fixed point, with `Q ≤ 1/(2γ)`.
* `iterD_ge_linear` and `exists_depth_exceeding` — **bootstrapping necessity**:
  when `4γD > 1` the noise grows at least linearly with slope
  `c = D - 1/(4γ) > 0`, so *every* decryption radius is exceeded after finitely
  many levels, and an explicit depth bound is given.
* `sqChain_noise_eq_iterD` — sharpness: over `ℤ` the recursion is *attained*, so
  the dichotomy is not an artefact of lossy bounding.
* `unbounded_depth_correct` / `bootstrap_needed_at_depth` — the two sides of the
  dichotomy transported back to statements about decrypting circuits.
-/

open FHENoise

-- open removed: section is not a namespace

noncomputable section

/-! ## 1. The quadratic noise map and its orbits -/







/-! ## 2. The stable regime -/





/-! ## 3. The unstable regime -/

open Finset BigOperators
open Polynomial
namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma gamma_pos : 0 < G.gamma := lt_of_lt_of_le zero_lt_one G.gamma_one_le

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma gamma_nonneg : 0 ≤ G.gamma := le_of_lt G.gamma_pos

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma nu_sub_le (x y : R) : G.nu (x - y) ≤ G.nu x + G.nu y := by
  have h := G.nu_add_le x (-y)
  rw [G.nu_neg] at h
  rwa [sub_eq_add_neg]

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma nu_le_of_sub (x y : R) : G.nu x ≤ G.nu y + G.nu (x - y) := by
  have h : G.nu (y + (x - y)) ≤ G.nu y + G.nu (x - y) := G.nu_add_le _ _
  simpa using h

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma nu_sum_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    G.nu (∑ i ∈ s, f i) ≤ ∑ i ∈ s, G.nu (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [G.nu_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (G.nu_add_le _ _) (by linarith)

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma gamma_nu_mul_le (x y : R) :
    G.gamma * G.nu (x * y) ≤ (G.gamma * G.nu x) * (G.gamma * G.nu y) := by
  have h := G.nu_mul_le x y
  have hg := G.gamma_nonneg
  nlinarith [G.nu_nonneg x, G.nu_nonneg y, G.gamma_pos]

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma nu_mul_le_bounds {x y : R} {a b : ℝ} (hx : G.nu x ≤ a) (hy : G.nu y ≤ b) :
    G.nu (x * y) ≤ G.gamma * a * b := by
  have hx0 := G.nu_nonneg x
  have hy0 := G.nu_nonneg y
  have ha : 0 ≤ a := le_trans hx0 hx
  calc G.nu (x * y) ≤ G.gamma * G.nu x * G.nu y := G.nu_mul_le x y
    _ ≤ G.gamma * a * G.nu y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx G.gamma_nonneg) hy0
    _ ≤ G.gamma * a * b := mul_le_mul_of_nonneg_left hy (mul_nonneg G.gamma_nonneg ha)

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma gamma_nu_pow_le (x : R) : ∀ n : ℕ, 1 ≤ n →
    G.gamma * G.nu (x ^ n) ≤ (G.gamma * G.nu x) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hik := ih hk
        have hstep : G.gamma * G.nu (x ^ k * x) ≤
            (G.gamma * G.nu (x ^ k)) * (G.gamma * G.nu x) :=
          G.gamma_nu_mul_le _ _
        have hxpos : 0 ≤ G.gamma * G.nu x :=
          mul_nonneg G.gamma_nonneg (G.nu_nonneg x)
        calc G.gamma * G.nu (x ^ (k + 1))
            = G.gamma * G.nu (x ^ k * x) := by rw [pow_succ]
          _ ≤ (G.gamma * G.nu (x ^ k)) * (G.gamma * G.nu x) := hstep
          _ ≤ (G.gamma * G.nu x) ^ k * (G.gamma * G.nu x) :=
              mul_le_mul_of_nonneg_right hik hxpos
          _ = (G.gamma * G.nu x) ^ (k + 1) := by rw [pow_succ]

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

lemma nu_nsmul_le (x : R) : ∀ n : ℕ, G.nu (n • x) ≤ n * G.nu x := by
  intro n
  induction n with
  | zero => simp [G.nu_zero]
  | succ k ih =>
      have : G.nu (k • x + x) ≤ G.nu (k • x) + G.nu x := G.nu_add_le _ _
      rw [succ_nsmul]
      push_cast
      linarith

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

@[simp] lemma rescale_nu (lam : ℝ) (h1 : 1 ≤ lam) (h2 : lam ≤ G.gamma) (x : R) :
    (G.rescale lam h1 h2).nu x = lam * G.nu x := rfl

end

end NoiseGauge

end FHENoise

namespace FHENoise

namespace NoiseGauge

section
variable {R : Type*} [CommRing R] (G : NoiseGauge R)

@[simp] lemma rescale_gamma (lam : ℝ) (h1 : 1 ≤ lam) (h2 : lam ≤ G.gamma) :
    (G.rescale lam h1 h2).gamma = G.gamma / lam := rfl

end

end NoiseGauge

end FHENoise

namespace FHENoise

@[simp] lemma intGauge_nu (x : ℤ) : intGauge.nu x = |(x : ℝ)| := rfl

end FHENoise

namespace FHENoise

@[simp] lemma intGauge_gamma : intGauge.gamma = 1 := rfl

end FHENoise

namespace FHENoise

section
variable {A : Type*}

@[simp] lemma l1Gauge_gamma (A : Type*) [AddCommMonoid A] : (l1Gauge A).gamma = 1 := rfl

end

end FHENoise

namespace FHENoise

section
variable {A : Type*}

@[simp] lemma l1Gauge_nu (A : Type*) [AddCommMonoid A] (f : AddMonoidAlgebra ℤ A) :
    (l1Gauge A).nu f = l1norm f := rfl

end

end FHENoise

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem phase_encryptWith (s scale m a e : R) :
    phase s (encryptWith s scale m a e) = scale * m + e := by
  simp only [phase, encryptWith]
  ring

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem phase_addCipher (s : R) (c d : Ciphertext R) :
    phase s (addCipher c d) = phase s c + phase s d := by
  simp only [phase, addCipher]
  ring

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem phase_add_encryptWith (s scale m m' a a' e e' : R) :
    phase s (addCipher (encryptWith s scale m a e)
      (encryptWith s scale m' a' e')) = scale * (m + m') + (e + e') := by
  rw [RingLWEFHE.phase_addCipher, RingLWEFHE.phase_encryptWith, RingLWEFHE.phase_encryptWith]
  ring

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem decrypt_add_encryptWith (s scale m m' a a' e e' : R)
    (decodePhase : R → R)
    (hdecode : Decodes decodePhase scale (m + m') (e + e')) :
    decryptWith s decodePhase
      (addCipher (encryptWith s scale m a e)
        (encryptWith s scale m' a' e')) = m + m' := by
  rw [decryptWith, RingLWEFHE.phase_add_encryptWith]
  exact hdecode

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem add_error_bound (e e' B : ℤ) (he : |e| ≤ B) (he' : |e'| ≤ B) :
    |e + e'| ≤ 2 * B := by
  calc
    |e + e'| ≤ |e| + |e'| := abs_add_le e e'
    _ ≤ B + B := add_le_add he he'
    _ = 2 * B := by ring

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem decrypt_add_of_noise_bound (s scale m m' a a' e e' B T : ℤ)
    (decodePhase : ℤ → ℤ)
    (hdecoder : CorrectBelow decodePhase scale T)
    (he : |e| ≤ B) (he' : |e'| ≤ B) (hbudget : 2 * B < T) :
    decryptWith s decodePhase
      (addCipher (encryptWith s scale m a e)
        (encryptWith s scale m' a' e')) = m + m' := by
  apply RingLWEFHE.decrypt_add_encryptWith
  apply hdecoder
  exact lt_of_le_of_lt (RingLWEFHE.add_error_bound e e' B he he') hbudget

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem gameGap_triangle {Ω : Type*} [Fintype Ω]
    (P Q U : FinitePMF Ω) : gameGap P U ≤ gameGap P Q + gameGap Q U := by
  simp only [gameGap, ← sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_sub_le _ _ _

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem gameGap_symm {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) :
    gameGap P Q = gameGap Q P := by
  simp [gameGap, abs_sub_comm]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]

theorem indCPA_of_decisional_ringLWE {Ω : Type*} [Fintype Ω]
    (challenge0 challenge1 ideal : FinitePMF Ω) (ε₀ ε₁ : ℝ)
    (hrlwe0 : gameGap challenge0 ideal ≤ ε₀)
    (hrlwe1 : gameGap challenge1 ideal ≤ ε₁) :
    gameGap challenge0 challenge1 ≤ ε₀ + ε₁ := by
  have htri := RingLWEFHE.gameGap_triangle challenge0 ideal challenge1
  rw [RingLWEFHE.gameGap_symm ideal challenge1] at htri
  exact le_trans htri (add_le_add hrlwe0 hrlwe1)

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem decrypt_refresh_encrypt (S : BootstrappableScheme M C) (m : M) :
    S.dec (S.refresh (S.enc m)) = m := by
  rw [S.refresh_correct, S.enc_correct]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem decrypt_refreshed_add (S : BootstrappableScheme M C) (c d : C) :
    S.dec (S.refresh (S.add c d)) = S.dec c + S.dec d := by
  rw [S.refresh_correct, S.add_correct]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem decrypt_refreshed_mul (S : BootstrappableScheme M C) (c d : C) :
    S.dec (S.refresh (S.mul c d)) = S.dec c * S.dec d := by
  rw [S.refresh_correct, S.mul_correct]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem Circuit.decrypt_evalEncrypted (S : BootstrappableScheme M C)
    (ρ : ℕ → C) (f : Circuit M) :
    S.dec (f.evalEncrypted S ρ) = f.eval (fun i => S.dec (ρ i)) := by
  induction f with
  | input i => exact S.refresh_correct (ρ i)
  | const m => exact RingLWEFHE.decrypt_refresh_encrypt S m
  | add f g ihf ihg =>
      rw [Circuit.evalEncrypted, RingLWEFHE.decrypt_refreshed_add, ihf, ihg, Circuit.eval]
  | mul f g ihf ihg =>
      rw [Circuit.evalEncrypted, RingLWEFHE.decrypt_refreshed_mul, ihf, ihg, Circuit.eval]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

def Circuit.mulDepth : Circuit M → ℕ
  | .input _ => 0
  | .const _ => 0
  | .add f g => max f.mulDepth g.mulDepth
  | .mul f g => max f.mulDepth g.mulDepth + 1

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem noiseAfterDepth_succ (B d : ℕ) :
    noiseAfterDepth B (d + 1) = noiseAfterDepth B d * noiseAfterDepth B d := by
  simp [noiseAfterDepth, pow_succ, pow_mul]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem supportsDepth_of_succ (B T d : ℕ) (hB : 0 < B)
    (h : SupportsDepth B T (d + 1)) : SupportsDepth B T d := by
  rw [SupportsDepth, RingLWEFHE.noiseAfterDepth_succ] at h
  have hpos : 0 < noiseAfterDepth B d := pow_pos hB _
  exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpos) h

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem concrete_depth_before_bootstrap :
    SupportsDepth 2 65536 3 ∧ ¬ SupportsDepth 2 65536 4 := by
  constructor <;> norm_num [SupportsDepth, noiseAfterDepth]

end

end RingLWEFHE

namespace RingLWEFHE

section
variable {R : Type*} [CommRing R]
variable {M C : Type*} [Semiring M]

theorem every_bounded_segment_safe (B T D : ℕ)
    (hmono : ∀ d ≤ D, noiseAfterDepth B d ≤ noiseAfterDepth B D)
    (hD : SupportsDepth B T D) :
    ∀ d ≤ D, SupportsDepth B T d := by
  intro d hd
  exact lt_of_le_of_lt (hmono d hd) hD

end

end RingLWEFHE

namespace FHENoise

section
variable {R : Type*} [CommRing R]

@[simp] lemma phaseHom_apply (s : R) (c : Cipher R) : phaseHom s c = phase s c := rfl

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

@[simp] lemma phase_add (s : R) (c d : Cipher R) :
    phase s (c + d) = phase s c + phase s d := by
  simp [phase]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

@[simp] lemma phase_C (s a : R) : phase s (C a) = a := by simp [phase]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

@[simp] lemma phase_mul (s : R) (c d : Cipher R) :
    phase s (c * d) = phase s c * phase s d := by
  simp [phase]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

lemma phase_ofPair (s : R) (c : RingLWEFHE.Ciphertext R) :
    phase s (ofPair c) = RingLWEFHE.phase s c := by
  simp [phase, ofPair, RingLWEFHE.phase]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

lemma ofPair_add (c d : RingLWEFHE.Ciphertext R) :
    ofPair (RingLWEFHE.addCipher c d) = ofPair c + ofPair d := by
  simp [ofPair, RingLWEFHE.addCipher, C_add]
  ring

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma noise_nonneg (s : R) (c : Cipher R) : 0 ≤ noise G s c := G.nu_nonneg _

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noise_add_le (s : R) (c d : Cipher R) :
    noise G s (c + d) ≤ noise G s c + noise G s d := by
  simpa [noise] using G.nu_add_le (phase s c) (phase s d)

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noise_mul_le (s : R) (c d : Cipher R) :
    noise G s (c * d) ≤ G.gamma * noise G s c * noise G s d := by
  simpa [noise] using G.nu_mul_le (phase s c) (phase s d)

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noise_relin_le {D : ℝ} (s : R) (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (c : Cipher R) :
    noise G s (relin c) ≤ noise G s c + D := by
  simp only [noise]
  exact le_trans (G.nu_le_of_sub _ _) (by linarith [hrelin c])

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noise_sum_le {ι : Type*} (s : R) (T : Finset ι) (f : ι → Cipher R) :
    noise G s (∑ i ∈ T, f i) ≤ ∑ i ∈ T, noise G s (f i) := by
  classical
  have hsum : phase s (∑ i ∈ T, f i) = ∑ i ∈ T, phase s (f i) := by
    simp [phase, Polynomial.eval_finset_sum]
  simpa [noise, hsum] using G.nu_sum_le T fun i => phase s (f i)

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem bgv_mul_noise_exact (t m e m' e' : R) :
    (m + t * e) * (m' + t * e') = m * m' + t * (e * m' + m * e' + t * (e * e')) := by
  ring

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem bgv_mul_noise_bound (t m e m' e' : R) {mu mu' eps eps' tau : ℝ}
    (hm : G.nu m ≤ mu) (hm' : G.nu m' ≤ mu') (he : G.nu e ≤ eps)
    (he' : G.nu e' ≤ eps') (ht : G.nu t ≤ tau) :
    G.nu (e * m' + m * e' + t * (e * e')) ≤
      G.gamma * (eps * mu' + mu * eps') + G.gamma ^ 2 * tau * (eps * eps') := by
  have hnn := G.nu_nonneg
  have h1 : G.nu (e * m') ≤ G.gamma * eps * mu' := G.nu_mul_le_bounds he hm'
  have h2 : G.nu (m * e') ≤ G.gamma * mu * eps' := G.nu_mul_le_bounds hm he'
  have hee : G.nu (e * e') ≤ G.gamma * eps * eps' := G.nu_mul_le_bounds he he'
  have h3 : G.nu (t * (e * e')) ≤ G.gamma * tau * (G.gamma * eps * eps') :=
    G.nu_mul_le_bounds ht hee
  have hsum := G.nu_add_le (e * m' + m * e') (t * (e * e'))
  have hsum2 := G.nu_add_le (e * m') (m * e')
  have hring1 : G.gamma * eps * mu' + G.gamma * mu * eps' =
      G.gamma * (eps * mu' + mu * eps') := by ring
  have hring2 : G.gamma * tau * (G.gamma * eps * eps') =
      G.gamma ^ 2 * tau * (eps * eps') := by ring
  linarith

end

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

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

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma noiseBound_mono {gamma D : ℝ} {beta beta' : ℕ → ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D)
    (hbeta : ∀ i, 0 ≤ beta i) (hle : ∀ i, beta i ≤ beta' i) :
    ∀ f : NoiseCkt, f.noiseBound gamma D beta ≤ f.noiseBound gamma D beta'
  | .leaf i => hle i
  | .add f g => by
      have := noiseBound_mono hg hD hbeta hle f
      have := noiseBound_mono hg hD hbeta hle g
      simp only [noiseBound]; linarith
  | .mul f g => by
      have h1 := noiseBound_mono hg hD hbeta hle f
      have h2 := noiseBound_mono hg hD hbeta hle g
      have p2 := FHENoise.NoiseCkt.noiseBound_nonneg hg hD hbeta g
      have hbeta' : ∀ i, 0 ≤ beta' i := fun i => le_trans (hbeta i) (hle i)
      have p1' := FHENoise.NoiseCkt.noiseBound_nonneg hg hD hbeta' f
      have hmm := mul_le_mul h1 h2 p2 p1'
      simp only [noiseBound]
      nlinarith [hmm, hg]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noise_evalEnc_le {D : ℝ} (G : NoiseGauge R) (s : R)
    (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D)
    (rho : ℕ → Cipher R) (beta : ℕ → ℝ) (hleaf : ∀ i, noise G s (rho i) ≤ beta i) :
    ∀ f : NoiseCkt, noise G s (f.evalEnc relin rho) ≤ f.noiseBound G.gamma D beta
  | .leaf i => hleaf i
  | .add f g => by
      have h1 := noise_evalEnc_le G s relin hrelin rho beta hleaf f
      have h2 := noise_evalEnc_le G s relin hrelin rho beta hleaf g
      have := FHENoise.noise_add_le G s (f.evalEnc relin rho) (g.evalEnc relin rho)
      simp only [evalEnc, noiseBound]
      linarith
  | .mul f g => by
      have h1 := noise_evalEnc_le G s relin hrelin rho beta hleaf f
      have h2 := noise_evalEnc_le G s relin hrelin rho beta hleaf g
      have hprod := FHENoise.noise_mul_le G s (f.evalEnc relin rho) (g.evalEnc relin rho)
      have hrel := FHENoise.noise_relin_le G s relin hrelin
        (f.evalEnc relin rho * g.evalEnc relin rho)
      have n1 := FHENoise.noise_nonneg G s (f.evalEnc relin rho)
      have n2 := FHENoise.noise_nonneg G s (g.evalEnc relin rho)
      have hg := G.gamma_nonneg
      have hbf := FHENoise.NoiseCkt.noiseBound_nonneg hg (le_trans (G.nu_nonneg _) (hrelin 0))
        (fun i => le_trans (FHENoise.noise_nonneg G s (rho i)) (hleaf i)) f
      have hmm := mul_le_mul h1 h2 n2 hbf
      simp only [evalEnc, noiseBound]
      nlinarith [hmm, hg, hprod, hrel]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem phase_eval_mod {M : Type*} [CommRing M] (s : R) (pi : R →+* M)
    (relin : Cipher R → Cipher R)
    (hrelin : ∀ c, pi (phase s (relin c)) = pi (phase s c))
    (rho : ℕ → Cipher R) :
    ∀ f : NoiseCkt,
      pi (phase s (f.evalEnc relin rho)) = f.evalPlain (fun i => pi (phase s (rho i)))
  | .leaf i => rfl
  | .add f g => by
      simp only [evalEnc, evalPlain, FHENoise.phase_add, map_add,
        phase_eval_mod s pi relin hrelin rho f, phase_eval_mod s pi relin hrelin rho g]
  | .mul f g => by
      simp only [evalEnc, evalPlain, hrelin, FHENoise.phase_mul, map_mul,
        phase_eval_mod s pi relin hrelin rho f, phase_eval_mod s pi relin hrelin rho g]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem decrypt_evalEnc {M : Type*} [CommRing M] {D T : ℝ} (G : NoiseGauge R) (s : R)
    (pi : R →+* M) (dec : R → M)
    (hdec : ∀ x, G.nu x < T → dec x = pi x)
    (relin : Cipher R → Cipher R)
    (hrelinN : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D)
    (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c))
    (rho : ℕ → Cipher R) (beta : ℕ → ℝ) (hleaf : ∀ i, noise G s (rho i) ≤ beta i)
    (f : NoiseCkt) (hbudget : f.noiseBound G.gamma D beta < T) :
    dec (phase s (f.evalEnc relin rho)) = f.evalPlain (fun i => pi (phase s (rho i))) := by
  have hnoise := FHENoise.NoiseCkt.noise_evalEnc_le G s relin hrelinN rho beta hleaf f
  rw [hdec _ (lt_of_le_of_lt hnoise hbudget)]
  exact phase_eval_mod s pi relin hrelinP rho f

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem evalEnc_subst (relin : Cipher R → Cipher R) (rho : ℕ → Cipher R)
    (g : ℕ → NoiseCkt) :
    ∀ f : NoiseCkt, (f.subst g).evalEnc relin rho
      = f.evalEnc relin (fun i => (g i).evalEnc relin rho)
  | .leaf i => rfl
  | .add f₁ f₂ => by
      simp only [subst, evalEnc, evalEnc_subst relin rho g f₁, evalEnc_subst relin rho g f₂]
  | .mul f₁ f₂ => by
      simp only [subst, evalEnc, evalEnc_subst relin rho g f₁, evalEnc_subst relin rho g f₂]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noiseBound_subst (gamma D : ℝ) (beta : ℕ → ℝ) (g : ℕ → NoiseCkt) :
    ∀ f : NoiseCkt, (f.subst g).noiseBound gamma D beta
      = f.noiseBound gamma D (fun i => (g i).noiseBound gamma D beta)
  | .leaf i => rfl
  | .add f₁ f₂ => by
      simp only [subst, noiseBound, noiseBound_subst gamma D beta g f₁,
        noiseBound_subst gamma D beta g f₂]
  | .mul f₁ f₂ => by
      simp only [subst, noiseBound, noiseBound_subst gamma D beta g f₁,
        noiseBound_subst gamma D beta g f₂]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem mulDepth_subst_le (g : ℕ → NoiseCkt) (Dg : ℕ) (hg : ∀ i, (g i).mulDepth ≤ Dg) :
    ∀ f : NoiseCkt, (f.subst g).mulDepth ≤ f.mulDepth + Dg
  | .leaf i => by simpa [subst, mulDepth] using hg i
  | .add f₁ f₂ => by
      have h1 := mulDepth_subst_le g Dg hg f₁
      have h2 := mulDepth_subst_le g Dg hg f₂
      simp only [subst, mulDepth]
      omega
  | .mul f₁ f₂ => by
      have h1 := mulDepth_subst_le g Dg hg f₁
      have h2 := mulDepth_subst_le g Dg hg f₂
      simp only [subst, mulDepth]
      omega

end

end NoiseCkt

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem gamma_iterNoise (gamma x : ℝ) :
    ∀ d : ℕ, gamma * iterNoise gamma d x = (gamma * x) ^ (2 ^ d)
  | 0 => by simp [iterNoise]
  | (d + 1) => by
      have ih := gamma_iterNoise gamma x d
      have hsq : gamma * (gamma * iterNoise gamma d x ^ 2) =
          (gamma * iterNoise gamma d x) ^ 2 := by ring
      rw [iterNoise, hsq, ih, ← pow_mul, pow_succ]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma iterNoise_nonneg {gamma : ℝ} (hg : 0 ≤ gamma) {x : ℝ} (hx : 0 ≤ x) :
    ∀ d, 0 ≤ iterNoise gamma d x
  | 0 => hx
  | (d + 1) => by
      have := iterNoise_nonneg hg hx d
      simp only [iterNoise]
      positivity

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma one_le_iterNoise {gamma x : ℝ} (hg : 1 ≤ gamma) (hx : 1 ≤ x) :
    ∀ d, 1 ≤ iterNoise gamma d x
  | 0 => hx
  | (d + 1) => by
      have ih := one_le_iterNoise hg hx d
      simp only [iterNoise]
      nlinarith

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma iterNoise_mono_input {gamma : ℝ} (hg : 0 ≤ gamma) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ∀ d, iterNoise gamma d x ≤ iterNoise gamma d y
  | 0 => hxy
  | (d + 1) => by
      have ih := iterNoise_mono_input hg hx hxy d
      have h0 := iterNoise_nonneg hg hx d
      have hsq := mul_self_le_mul_self h0 ih
      simp only [iterNoise]
      nlinarith [hsq, hg]

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma iterNoise_mono_depth {gamma x : ℝ} (hg : 1 ≤ gamma) (hx : 1 ≤ x) :
    ∀ {d e : ℕ}, d ≤ e → iterNoise gamma d x ≤ iterNoise gamma e x := by
  intro d e hde
  induction e with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.lt_or_ge d (k + 1) with h | h
      · have hk : d ≤ k := Nat.lt_succ_iff.mp h
        have h1 := ih hk
        have h2 := FHENoise.one_le_iterNoise hg hx k
        simp only [iterNoise]
        nlinarith
      · have : d = k + 1 := le_antisymm hde h
        subst this
        exact le_refl _

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma iterNoise_superadd {gamma : ℝ} (hg : 0 ≤ gamma) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∀ d, iterNoise gamma d x + iterNoise gamma d y ≤ iterNoise gamma d (x + y)
  | 0 => by simp [iterNoise]
  | (d + 1) => by
      have ih := iterNoise_superadd hg hx hy d
      have hx0 := iterNoise_nonneg hg hx d
      have hy0 := iterNoise_nonneg hg hy d
      have hxy0 := iterNoise_nonneg hg (by linarith : (0:ℝ) ≤ x + y) d
      have hsq := mul_self_le_mul_self (by linarith : (0:ℝ) ≤
        iterNoise gamma d x + iterNoise gamma d y) ih
      simp only [iterNoise]
      nlinarith [hsq, hg, mul_nonneg hx0 hy0]

end

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

lemma one_le_leafCount (f : NoiseCkt) : 1 ≤ f.leafCount := by
  induction f with
  | leaf i => simp [leafCount]
  | add f g ihf ihg => simp only [leafCount]; omega
  | mul f g ihf ihg => simp only [leafCount]; omega

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem noiseBound_le_iter {gamma B : ℝ} (hg : 1 ≤ gamma) (hB : 1 ≤ B) :
    ∀ f : NoiseCkt,
      f.noiseBound gamma 0 (fun _ => B) ≤ iterNoise gamma f.mulDepth (f.leafCount * B)
  | .leaf i => by simp [noiseBound, leafCount, mulDepth, iterNoise]
  | .add f g => by
      have h1 := noiseBound_le_iter hg hB f
      have h2 := noiseBound_le_iter hg hB g
      have hg0 : (0:ℝ) ≤ gamma := by linarith
      have hLf : (1:ℝ) ≤ (f.leafCount : ℝ) * B := by
        have : (1:ℝ) ≤ (f.leafCount : ℝ) := by exact_mod_cast f.one_le_leafCount
        nlinarith
      have hLg : (1:ℝ) ≤ (g.leafCount : ℝ) * B := by
        have : (1:ℝ) ≤ (g.leafCount : ℝ) := by exact_mod_cast g.one_le_leafCount
        nlinarith
      have d1 : iterNoise gamma f.mulDepth ((f.leafCount : ℝ) * B) ≤
          iterNoise gamma (max f.mulDepth g.mulDepth) ((f.leafCount : ℝ) * B) :=
        iterNoise_mono_depth hg hLf (le_max_left _ _)
      have d2 : iterNoise gamma g.mulDepth ((g.leafCount : ℝ) * B) ≤
          iterNoise gamma (max f.mulDepth g.mulDepth) ((g.leafCount : ℝ) * B) :=
        iterNoise_mono_depth hg hLg (le_max_right _ _)
      have hsuper := FHENoise.iterNoise_superadd hg0 (by linarith : (0:ℝ) ≤ (f.leafCount : ℝ) * B)
        (by linarith : (0:ℝ) ≤ (g.leafCount : ℝ) * B) (max f.mulDepth g.mulDepth)
      have hcast : ((f.leafCount + g.leafCount : ℕ) : ℝ) * B =
          (f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B := by push_cast; ring
      simp only [noiseBound, mulDepth, leafCount, hcast]
      linarith
  | .mul f g => by
      have h1 := noiseBound_le_iter hg hB f
      have h2 := noiseBound_le_iter hg hB g
      have hg0 : (0:ℝ) ≤ gamma := by linarith
      have hLf : (1:ℝ) ≤ (f.leafCount : ℝ) * B := by
        have : (1:ℝ) ≤ (f.leafCount : ℝ) := by exact_mod_cast f.one_le_leafCount
        nlinarith
      have hLg : (1:ℝ) ≤ (g.leafCount : ℝ) * B := by
        have : (1:ℝ) ≤ (g.leafCount : ℝ) := by exact_mod_cast g.one_le_leafCount
        nlinarith
      have hsumL : (1:ℝ) ≤ (f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B := by linarith
      have d1 : iterNoise gamma f.mulDepth ((f.leafCount : ℝ) * B) ≤
          iterNoise gamma (max f.mulDepth g.mulDepth)
            ((f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B) := by
        refine le_trans (iterNoise_mono_depth hg hLf (le_max_left f.mulDepth g.mulDepth)) ?_
        exact FHENoise.iterNoise_mono_input hg0 (by linarith) (by linarith) _
      have d2 : iterNoise gamma g.mulDepth ((g.leafCount : ℝ) * B) ≤
          iterNoise gamma (max f.mulDepth g.mulDepth)
            ((f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B) := by
        refine le_trans (iterNoise_mono_depth hg hLg (le_max_right f.mulDepth g.mulDepth)) ?_
        exact FHENoise.iterNoise_mono_input hg0 (by linarith) (by linarith) _
      have p1 := FHENoise.NoiseCkt.noiseBound_nonneg hg0 (le_refl (0:ℝ))
        (fun _ => by linarith : ∀ _ : ℕ, (0:ℝ) ≤ B) f
      have p2 := FHENoise.NoiseCkt.noiseBound_nonneg hg0 (le_refl (0:ℝ))
        (fun _ => by linarith : ∀ _ : ℕ, (0:ℝ) ≤ B) g
      have hpos : 0 ≤ iterNoise gamma (max f.mulDepth g.mulDepth)
          ((f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B) :=
        iterNoise_nonneg hg0 (by linarith) _
      have hcast : ((f.leafCount + g.leafCount : ℕ) : ℝ) * B =
          (f.leafCount : ℝ) * B + (g.leafCount : ℝ) * B := by push_cast; ring
      have hfX := le_trans h1 d1
      have hgX := le_trans h2 d2
      have hprod := mul_le_mul hfX hgX p2 hpos
      simp only [noiseBound, mulDepth, leafCount, hcast, iterNoise]
      nlinarith [hprod, hg0, hpos]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

@[simp] lemma sqChain_mulDepth : ∀ d, (sqChain d).mulDepth = d
  | 0 => rfl
  | (d + 1) => by simp [sqChain, mulDepth, sqChain_mulDepth d]

end

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

section
variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

theorem sqChain_noise_eq (s b : ℤ) (rho : ℕ → Cipher ℤ) (hrho : phase s (rho 0) = b) :
    ∀ d, noise intGauge s ((sqChain d).evalEnc id rho) = |(b : ℝ)| ^ (2 ^ d)
  | 0 => by simp [sqChain, evalEnc, noise, hrho]
  | (d + 1) => by
      have ih := sqChain_noise_eq s b rho hrho d
      set x := phase s ((sqChain d).evalEnc id rho) with hxdef
      have hphase : phase s ((sqChain (d + 1)).evalEnc id rho) = x * x := by
        simp [sqChain, evalEnc, hxdef]
      have h2 : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      simp only [noise, hphase, FHENoise.intGauge_nu] at ih ⊢
      push_cast
      rw [abs_mul, ih, h2, pow_add]

end

end NoiseCkt

end FHENoise

namespace FHENoise

@[simp] lemma iterD_zero (gamma D x : ℝ) : iterD gamma D 0 x = x := rfl

end FHENoise

namespace FHENoise

@[simp] lemma iterD_succ (gamma D x : ℝ) (d : ℕ) :
    iterD gamma D (d + 1) x = noiseStep gamma D (iterD gamma D d x) := rfl

end FHENoise

namespace FHENoise

lemma iterD_nonneg {gamma D x : ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D) (hx : 0 ≤ x) :
    ∀ d, 0 ≤ iterD gamma D d x
  | 0 => hx
  | (d + 1) => by
      have := iterD_nonneg hg hD hx d
      simp only [FHENoise.iterD_succ, noiseStep]
      positivity

end FHENoise

namespace FHENoise

lemma iterD_zero_relin (gamma x : ℝ) : ∀ d, iterD gamma 0 d x = iterNoise gamma d x
  | 0 => rfl
  | (d + 1) => by simp [iterD, noiseStep, iterNoise, iterD_zero_relin gamma x d]

end FHENoise

namespace FHENoise

theorem iterD_le_of_invariant {gamma D Q x : ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D)
    (hQ : InvariantBudget gamma D Q) (hx0 : 0 ≤ x) (hx : x ≤ Q) :
    ∀ d, iterD gamma D d x ≤ Q
  | 0 => hx
  | (d + 1) => by
      have ih := iterD_le_of_invariant hg hD hQ hx0 hx d
      have hpos := FHENoise.iterD_nonneg hg hD hx0 d
      have hstep : gamma * (iterD gamma D d x) ^ 2 ≤ gamma * Q ^ 2 := by
        have hsq := mul_self_le_mul_self hpos ih
        nlinarith [hsq, hg]
      have := hQ.2
      simp only [FHENoise.iterD_succ, noiseStep] at *
      linarith

end FHENoise

namespace FHENoise

theorem noiseFixedPoint_spec {gamma D : ℝ} (hg : 0 < gamma) (hD : 0 ≤ D)
    (hdisc : 4 * gamma * D ≤ 1) :
    noiseStep gamma D (noiseFixedPoint gamma D) = noiseFixedPoint gamma D ∧
      0 ≤ noiseFixedPoint gamma D ∧ noiseFixedPoint gamma D ≤ 1 / (2 * gamma) := by
  set r := Real.sqrt (1 - 4 * gamma * D) with hr
  have hnn : 0 ≤ 1 - 4 * gamma * D := by linarith
  have hr2 : r ^ 2 = 1 - 4 * gamma * D := Real.sq_sqrt hnn
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := by
    nlinarith [hr2, hr0, mul_nonneg (le_of_lt hg) hD]
  have h2g : 0 < 2 * gamma := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hfix : noiseStep gamma D ((1 - r) / (2 * gamma)) = (1 - r) / (2 * gamma) := by
      rw [noiseStep]
      field_simp
      nlinarith [hr2]
    simpa only [noiseFixedPoint, ← hr] using hfix
  · simp only [noiseFixedPoint, ← hr]
    apply div_nonneg (by linarith) (le_of_lt h2g)
  · simp only [noiseFixedPoint, ← hr]
    rw [div_le_div_iff_of_pos_right h2g]
    linarith

end FHENoise

namespace FHENoise

theorem noiseStep_ge_add {gamma D : ℝ} (hg : 0 < gamma) (x : ℝ) :
    x + (D - 1 / (4 * gamma)) ≤ noiseStep gamma D x := by
  have hkey : gamma * (x - 1 / (2 * gamma)) ^ 2 ≥ 0 := by positivity
  have hexpand : gamma * (x - 1 / (2 * gamma)) ^ 2
      = gamma * x ^ 2 - x + 1 / (4 * gamma) := by
    field_simp
    ring
  simp only [noiseStep]
  linarith [hexpand ▸ hkey]

end FHENoise

namespace FHENoise

theorem iterD_ge_linear {gamma D x : ℝ} (hg : 0 < gamma) :
    ∀ d : ℕ, x + d * (D - 1 / (4 * gamma)) ≤ iterD gamma D d x
  | 0 => by simp
  | (d + 1) => by
      have ih := iterD_ge_linear (gamma := gamma) (D := D) (x := x) hg d
      have hstep := FHENoise.noiseStep_ge_add (D := D) hg (iterD gamma D d x)
      have : ((d : ℝ) + 1) * (D - 1 / (4 * gamma))
          = (d : ℝ) * (D - 1 / (4 * gamma)) + (D - 1 / (4 * gamma)) := by ring
      simp only [FHENoise.iterD_succ, Nat.cast_succ, this]
      linarith

end FHENoise

namespace FHENoise

theorem exists_depth_exceeding {gamma D x : ℝ} (hg : 0 < gamma)
    (hunstable : 1 < 4 * gamma * D) (T : ℝ) :
    ∃ d : ℕ, T < iterD gamma D d x := by
  have hc : 0 < D - 1 / (4 * gamma) := by
    have h4 : 0 < 4 * gamma := by linarith
    rw [sub_pos, div_lt_iff₀ h4]
    linarith
  obtain ⟨d, hd⟩ := exists_nat_gt ((T - x) / (D - 1 / (4 * gamma)))
  refine ⟨d, lt_of_lt_of_le ?_ (FHENoise.iterD_ge_linear (gamma := gamma) (D := D) (x := x) hg d)⟩
  have := (div_lt_iff₀ hc).mp hd
  linarith

end FHENoise

namespace FHENoise

theorem noiseStep_dichotomy {gamma D : ℝ} (hg : 0 < gamma) (hD : 0 ≤ D) :
    (∃ Q, InvariantBudget gamma D Q) ↔ 4 * gamma * D ≤ 1 := by
  constructor
  · rintro ⟨Q, -, hQ⟩
    simp only [noiseStep] at hQ
    nlinarith [sq_nonneg (2 * gamma * Q - 1)]
  · intro hdisc
    obtain ⟨hfix, hnn, -⟩ := FHENoise.noiseFixedPoint_spec hg hD hdisc
    exact ⟨noiseFixedPoint gamma D, hnn, le_of_eq hfix⟩

end FHENoise

namespace FHENoise

lemma le_noiseStep_of_le_fixedPoint {gamma D Q y : ℝ} (hg : 0 < gamma)
    (hQfix : noiseStep gamma D Q = Q) (hQle : Q ≤ 1 / (2 * gamma))
    (hy : y ≤ Q) : y ≤ noiseStep gamma D y := by
  have h2g : 0 < 2 * gamma := by linarith
  have hQ2 : 2 * gamma * Q ≤ 1 := by
    rw [le_div_iff₀ h2g] at hQle
    linarith
  have hD : D = Q - gamma * Q ^ 2 := by
    rw [noiseStep] at hQfix; linarith
  have hfac : gamma * y ^ 2 + D - y = (Q - y) * (1 - gamma * (y + Q)) := by
    rw [hD]; ring
  have hpos : 0 ≤ (Q - y) * (1 - gamma * (y + Q)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  simp only [noiseStep]
  linarith

end FHENoise

namespace FHENoise

theorem tendsto_iterD_fixedPoint {gamma D Q x : ℝ} (hg : 0 < gamma) (hD : 0 ≤ D)
    (hQfix : noiseStep gamma D Q = Q) (hQ0 : 0 ≤ Q) (hQle : Q ≤ 1 / (2 * gamma))
    (hx0 : 0 ≤ x) (hx : x ≤ Q) :
    Filter.Tendsto (fun d => iterD gamma D d x) Filter.atTop (nhds Q) := by
  have hg0 : (0:ℝ) ≤ gamma := le_of_lt hg
  have hinv : InvariantBudget gamma D Q := ⟨hQ0, le_of_eq hQfix⟩
  have hle : ∀ d, iterD gamma D d x ≤ Q := FHENoise.iterD_le_of_invariant hg0 hD hinv hx0 hx
  have hnn : ∀ d, 0 ≤ iterD gamma D d x := FHENoise.iterD_nonneg hg0 hD hx0
  have hmono : Monotone fun d => iterD gamma D d x := by
    refine monotone_nat_of_le_succ fun d => ?_
    simpa [FHENoise.iterD_succ] using
      le_noiseStep_of_le_fixedPoint hg hQfix hQle (hle d)
  have hbdd : BddAbove (Set.range fun d => iterD gamma D d x) :=
    ⟨Q, by rintro y ⟨d, rfl⟩; exact hle d⟩
  set L := ⨆ d, iterD gamma D d x with hL
  have htend : Filter.Tendsto (fun d => iterD gamma D d x) Filter.atTop (nhds L) :=
    tendsto_atTop_ciSup hmono hbdd
  have hcont : Continuous (noiseStep gamma D) := by
    unfold noiseStep; fun_prop
  have hshift : Filter.Tendsto (fun d => iterD gamma D (d + 1) x) Filter.atTop (nhds L) :=
    htend.comp (Filter.tendsto_add_atTop_nat 1)
  have hstep : Filter.Tendsto (fun d => iterD gamma D (d + 1) x) Filter.atTop
      (nhds (noiseStep gamma D L)) := by
    simpa [FHENoise.iterD_succ] using (hcont.tendsto L).comp htend
  have hfixL : noiseStep gamma D L = L := tendsto_nhds_unique hstep hshift
  have hLQ : L ≤ Q := ciSup_le hle
  have hL0 : 0 ≤ L := le_trans (hnn 0) (le_ciSup hbdd 0)
  have h2g : 0 < 2 * gamma := by linarith
  have hQ2 : 2 * gamma * Q ≤ 1 := by
    rw [le_div_iff₀ h2g] at hQle
    linarith
  have hfac : (L - Q) * (gamma * (L + Q) - 1) = 0 := by
    have h1 : gamma * L ^ 2 + D = L := hfixL
    have h2 : gamma * Q ^ 2 + D = Q := hQfix
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hfac with h | h
  · have : L = Q := by linarith
    rwa [this] at htend
  · have : L = Q := by nlinarith
    rwa [this] at htend

end FHENoise

namespace FHENoise

namespace NoiseCkt

theorem noiseBound_sqChain (gamma D B : ℝ) :
    ∀ d, (sqChain d).noiseBound gamma D (fun _ => B) = iterD gamma D d B
  | 0 => rfl
  | (d + 1) => by
      rw [sqChain, noiseBound, noiseBound_sqChain gamma D B d, FHENoise.iterD_succ, noiseStep]
      ring

end NoiseCkt

end FHENoise

namespace FHENoise

namespace NoiseCkt

theorem sqChain_noise_eq_iterD (s b k : ℤ) (hb : 0 ≤ b) (hk : 0 ≤ k) :
    ∀ d, noise intGauge s
        ((sqChain d).evalEnc (fun c => c + Polynomial.C k) (fun _ => Polynomial.C b))
      = iterD 1 (k : ℝ) d (b : ℝ) := by
  have key : ∀ d, ∃ v : ℤ, 0 ≤ v ∧
      phase s ((sqChain d).evalEnc (fun c => c + Polynomial.C k)
        (fun _ => Polynomial.C b)) = v ∧ (v : ℝ) = iterD 1 (k : ℝ) d (b : ℝ) := by
    intro d
    induction d with
    | zero => exact ⟨b, hb, by simp [sqChain, evalEnc, phase], by simp⟩
    | succ d ih =>
        obtain ⟨v, hv0, hv, hvr⟩ := ih
        refine ⟨v * v + k, by positivity, ?_, ?_⟩
        · simp only [sqChain, evalEnc, FHENoise.phase_add, FHENoise.phase_mul, FHENoise.phase_C, hv]
        · push_cast
          rw [hvr]
          simp only [FHENoise.iterD_succ, noiseStep, sq]
          ring
  intro d
  obtain ⟨v, hv0, hv, hvr⟩ := key d
  have : (0:ℝ) ≤ (v : ℝ) := by exact_mod_cast hv0
  simp only [noise, hv, FHENoise.intGauge_nu]
  rw [abs_of_nonneg this, hvr]

end NoiseCkt

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

theorem unbounded_depth_correct {M : Type*} [CommRing M] {D T B Q : ℝ}
    (G : NoiseGauge R) (s : R) (pi : R →+* M) (dec : R → M)
    (hdec : ∀ x, G.nu x < T → dec x = pi x)
    (relin : Cipher R → Cipher R)
    (hrelinN : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
    (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c))
    (rho : ℕ → Cipher R) (hleaf : ∀ i, noise G s (rho i) ≤ B) (hB : 0 ≤ B)
    (hQ : InvariantBudget G.gamma D Q) (hBQ : B ≤ Q) (hT : Q < T) (d : ℕ) :
    dec (phase s ((NoiseCkt.sqChain d).evalEnc relin rho))
      = (NoiseCkt.sqChain d).evalPlain (fun i => pi (phase s (rho i))) := by
  have hbudget : (NoiseCkt.sqChain d).noiseBound G.gamma D (fun _ => B) < T := by
    rw [NoiseCkt.noiseBound_sqChain]
    exact lt_of_le_of_lt
      (FHENoise.iterD_le_of_invariant G.gamma_nonneg hD hQ hB hBQ d) hT
  exact NoiseCkt.decrypt_evalEnc G s pi dec hdec relin hrelinN hrelinP rho
    (fun _ => B) hleaf _ hbudget

end

end FHENoise

namespace FHENoise

section
variable {R : Type*} [CommRing R]

theorem bootstrap_needed_at_depth (s b k : ℤ) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hunstable : 1 < 4 * (k : ℝ)) (T : ℝ) :
    ∃ d : ℕ, T < noise intGauge s
      ((NoiseCkt.sqChain d).evalEnc (fun c => c + Polynomial.C k)
        (fun _ => Polynomial.C b)) := by
  obtain ⟨d, hd⟩ := FHENoise.exists_depth_exceeding (gamma := 1) (D := (k : ℝ)) (x := (b : ℝ))
    one_pos (by linarith) T
  exact ⟨d, by rw [NoiseCkt.sqChain_noise_eq_iterD s b k hb hk d]; exact hd⟩

end

end FHENoise


theorem solution {gamma D x : ℝ} (hg : 0 < gamma)
    (hunstable : 1 < 4 * gamma * D) (T : ℝ) :
    ∃ d : ℕ, T < iterD gamma D d x := by
  have hc : 0 < D - 1 / (4 * gamma) := by
    have h4 : 0 < 4 * gamma := by linarith
    rw [sub_pos, div_lt_iff₀ h4]
    linarith
  obtain ⟨d, hd⟩ := exists_nat_gt ((T - x) / (D - 1 / (4 * gamma)))
  refine ⟨d, lt_of_lt_of_le ?_ (FHENoise.iterD_ge_linear (gamma := gamma) (D := D) (x := x) hg d)⟩
  have := (div_lt_iff₀ hc).mp hd
  linarith

#print axioms solution
