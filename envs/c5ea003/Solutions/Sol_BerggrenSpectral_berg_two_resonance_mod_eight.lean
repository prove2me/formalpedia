-- Prove2me | solution 1 for BerggrenSpectral.berg_two_resonance_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:03:45.145993+00:00
-- url     : https://prove2.me/submissions/d6d1fe22-e129-46fb-97ea-be517d458760

-- Sol generated from Cryptography/BerggrenSpectral/HyperbolicResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_berg_two_resonance_nqr
import Theorems.Thm_BerggrenSpectral_berg_two_resonance_qr
import Theorems.Thm_BerggrenSpectral_two_chi_cases
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








/-! ## Algebraic identities for the hyperbolic block -/





/-! ## Frobenius over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]








/-! ## Transport back to `M₂` -/











open BerggrenSpectral in
theorem solution(hp : p ≠ 2) :
    (p % 8 = 1 ∨ p % 8 = 7 → (redMat p M₂) ^ (p - 1) = 1) ∧
    (p % 8 = 3 ∨ p % 8 = 5 → (redMat p M₂) ^ (p + 1) = 1) := by
  have hne : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_prime p hp
  have hhalf : p / 2 = (p - 1) / 2 := by
    have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
    obtain ⟨t, ht⟩ := hodd; omega
  constructor
  · intro h8
    have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp).mpr h8
    have := (ZMod.euler_criterion p hne).mp hsq
    rw [hhalf] at this
    exact berg_two_resonance_qr p hp this
  · intro h8
    have hsq : ¬ IsSquare (2 : ZMod p) := by
      intro hs
      rcases (ZMod.exists_sq_eq_two_iff hp).mp hs with h | h <;> omega
    have hne1 : (2 : ZMod p) ^ ((p - 1) / 2) ≠ 1 := by
      intro hcon
      exact hsq ((ZMod.euler_criterion p hne).mpr (by rw [hhalf]; exact hcon))
    rcases two_chi_cases p hp with h | h
    · exact absurd h hne1
    · exact berg_two_resonance_nqr p hp h
