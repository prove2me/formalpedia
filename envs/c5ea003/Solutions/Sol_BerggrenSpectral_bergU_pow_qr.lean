-- Prove2me | solution 1 for BerggrenSpectral.bergU_pow_qr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:52:01.399672+00:00
-- url     : https://prove2.me/submissions/06a8ea5f-3abb-4e1e-9f83-9a987e0e5b52

-- Sol generated from Cryptography/BerggrenSpectral/HyperbolicResonance.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_bergU_frob

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


theorem bergU_eq : bergU R = (3 : R) • 1 + bergS R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bergU, bergS]

/-- `U⁻¹ = 6 - U`: the hyperbolic block is a unit of determinant `1`. -/
theorem bergU_inv : bergU R * ((6 : R) • 1 - bergU R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bergU, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring


/-! ## Frobenius over `ZMod p` -/

variable (p : ℕ) [Fact p.Prime]


/-- The quadratic character of `2` controls the Frobenius twist, because `8 = 2³` and the
character takes values `±1`. -/
theorem eight_pow_eq_two_pow :
    (8 : ZMod p) ^ ((p - 1) / 2) = ((2 : ZMod p) ^ ((p - 1) / 2)) ^ 3 := by
  rw [show (8 : ZMod p) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]






/-! ## Transport back to `M₂` -/











open BerggrenSpectral in
theorem solution(hp : p ≠ 2) (h : (2 : ZMod p) ^ ((p - 1) / 2) = 1) :
    (bergU (ZMod p)) ^ (p - 1) = 1 := by
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le.trans' (by norm_num)
  have hfrob : (bergU (ZMod p)) ^ p = bergU (ZMod p) := by
    rw [bergU_frob p hp, eight_pow_eq_two_pow p, h, one_pow, one_smul, ← bergU_eq]
  have hsucc : (bergU (ZMod p)) ^ (p - 1) * bergU (ZMod p) = (bergU (ZMod p)) ^ p := by
    rw [← pow_succ]; congr 1; omega
  calc (bergU (ZMod p)) ^ (p - 1)
      = (bergU (ZMod p)) ^ (p - 1) * (bergU (ZMod p) * ((6 : ZMod p) • 1 - bergU (ZMod p))) := by
        rw [bergU_inv, mul_one]
    _ = ((bergU (ZMod p)) ^ (p - 1) * bergU (ZMod p)) * ((6 : ZMod p) • 1 - bergU (ZMod p)) := by
        rw [mul_assoc]
    _ = bergU (ZMod p) * ((6 : ZMod p) • 1 - bergU (ZMod p)) := by rw [hsucc, hfrob]
    _ = 1 := bergU_inv
