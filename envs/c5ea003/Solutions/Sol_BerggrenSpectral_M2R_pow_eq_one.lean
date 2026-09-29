-- Prove2me | solution 1 for BerggrenSpectral.M2R_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:49:52.610687+00:00
-- url     : https://prove2.me/submissions/d3a66706-d3db-41e4-920a-5df2a5046fc0

-- Sol generated from Cryptography/BerggrenSpectral/HyperbolicResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_bergV_pow
import Theorems.Thm_BerggrenSpectral_berg_pow_conj
import Theorems.Thm_BerggrenSpectral_det_bergW
import Theorems.Thm_BerggrenSpectral_two_ne_zero_of_odd_prime

/-!
# Hyperbolic Berggren Resonance: the frequencies `2(p ∓ 1)`

The middle Berggren generator `M₂` is hyperbolic, with spectrum `{-1, 3 + 2√2, 3 - 2√2}`
(`berg_charpoly_two`).  This file proves that **modulo a prime `p` the resonant exponent of
`M₂` is `2(p - 1)` or `2(p + 1)` according to the quadratic character of `2`, i.e. according
to `p mod 8`** — the "energy frequency" of the hyperbolic branch is locked to the prime.

The proof is a fully explicit Frobenius computation.

1.  `berg_conj`: the integral conjugation `M₂ * W = W * V`, where the columns of
    `W = !![1,0,1; 1,0,-1; 0,1,0]` are the invariant vectors `(1,1,0)`, `(0,0,1)` and the
    `-1`-eigenvector `(1,-1,0)`, and `V` is block diagonal with blocks `U = !![3,2;4,3]`
    and `(-1)`.
2.  `bergU_frob`: over `ZMod p`, `U = 3 + S` with `S² = 8`, so the Frobenius endomorphism
    gives `U ^ p = 3 + 8^((p-1)/2) • S`; this is the matrix incarnation of
    `(3 + 2√2)^p = 3 ± 2√2` in `𝔽_p(√2)`.
3.  Hence `U ^ (p - 1) = 1` when `2` is a square mod `p` and `U ^ (p + 1) = 1` otherwise
    (`bergU_pow_qr`, `bergU_pow_nqr`), because `U⁻¹ = 6 - U`.
4.  Transporting back through `W` (invertible because `det W = -2` and `p` is odd) and
    squaring to kill the `-1` eigenvalue yields the main theorems
    `berg_two_resonance_qr`, `berg_two_resonance_nqr`, `berg_two_resonance_mod_eight`
    and the uniform `berg_two_resonance` : `M₂ ^ (2 * (p² - 1)) ≡ 1 (mod p)`.

This is the exact analogue, for the Pythagorean/Berggren tree, of the Lucas–Lehmer and
Pollard `p ± 1` phenomena; the factoring consequences are in `Factorization.lean`.
-/

open BerggrenSpectral

open Matrix

variable (R : Type*) [CommRing R]

/-! ## The hyperbolic block and the conjugating matrix -/







variable {R}


theorem blockEmbed_one : blockEmbed R (1 : Matrix (Fin 2) (Fin 2) R) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockEmbed]






/-! ## Algebraic identities for the hyperbolic block -/





/-! ## Frobenius over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]








/-! ## Transport back to `M₂` -/











open BerggrenSpectral in
theorem solution(hp : p ≠ 2) {k : ℕ} (hU : (bergU (ZMod p)) ^ k = 1) (hk : Even k) :
    (M2R (ZMod p)) ^ k = 1 := by
  have hdet : IsUnit (bergW (ZMod p)).det := by
    rw [det_bergW]
    exact (isUnit_iff_ne_zero).mpr (two_ne_zero_of_odd_prime p hp)
  haveI : Invertible (bergW (ZMod p)) := invertibleOfIsUnitDet _ hdet
  have hV : (bergV (ZMod p)) ^ k = 1 := by
    rw [bergV_pow, hU, hk.neg_one_pow, blockEmbed_one]
  have h := berg_pow_conj (R := ZMod p) k
  rw [hV, mul_one] at h
  have h1 : (M2R (ZMod p)) ^ k * bergW (ZMod p) = 1 * bergW (ZMod p) := by rw [h, one_mul]
  exact mul_left_injective_of_invertible (bergW (ZMod p)) h1
