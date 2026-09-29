-- Prove2me | solution 1 for BerggrenSpectral.two_ne_zero_of_odd_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:57.25975+00:00
-- url     : https://prove2.me/submissions/1c0dc794-b570-423e-9c4c-f126e6cec23a

-- Sol generated from Cryptography/BerggrenSpectral/HyperbolicResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance

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








/-! ## Algebraic identities for the hyperbolic block -/





/-! ## Frobenius over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]








/-! ## Transport back to `M₂` -/











open BerggrenSpectral in
theorem solution(hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
  have hd' : p ∣ 2 := by exact_mod_cast hd
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd')
