-- Prove2me | solution 1 for BerggrenSpectral.redMat_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:53:40.563409+00:00
-- url     : https://prove2.me/submissions/6ea628fb-06f3-4734-a7e7-5da516edec00

-- Sol generated from Cryptography/BerggrenSpectral/Factorization.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_redMat_apply

/-!
# Resonance ⇒ Factorization: extracting a prime factor of `N = p q`

Combining the exact spectral analysis of the previous files we obtain a **provably correct
factoring criterion** for RSA-type moduli `N = p q`, driven by the hyperbolic Berggren
generator `M₂`.

The mechanism ("modular energy resonance") is:

* `berg_two_resonance_qr` / `berg_two_resonance_nqr`: modulo the prime `p` the generator `M₂`
  has resonant frequency dividing `p - 1` or `p + 1` (hence `p² - 1`), decided by `p mod 8`;
* if an exponent `k` is *in resonance with `p` but out of resonance with `q`*, then `M₂ ^ k - 1`
  is divisible by `p` entrywise but has some entry not divisible by `q`;
* `berg_resonance_extracts_factor`: the gcd of that entry with `N` is then **exactly `p`**, a
  nontrivial factor of `N`.

`berg_resonance_factorization` packages this with the canonical resonant exponent
`k = p² - 1`, and `berg_resonance_sharp_frequency` with the sharp frequencies `p ∓ 1`.
Finally `berg_factor_fifteen` is a fully checked concrete instance: at the resonant
frequency `4 = 3 + 1` for `p = 3`, the criterion splits `N = 15`.

The contrast with `berg_one_gcd_barrier` (unipotent branch: no factoring information at all)
is the main structural finding of this development: **only the hyperbolic branch of the
Berggren tree carries prime-separating spectral information.**
-/

open BerggrenSpectral

open Matrix

/-! ## From matrix congruences to divisibility -/


/-! ## The gcd extraction step -/


/-! ## The main factoring theorem -/






/-! ## A concrete verified instance: `N = 15 = 3 · 5` -/




/-! ## A textbook RSA modulus: `N = 3233 = 53 · 61` -/





open BerggrenSpectral in
theorem solution(N : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    redMat N A = 1 ↔ ∀ i j, (N : ℤ) ∣ (A - 1) i j := by
  have hmap : redMat N (A - 1) = redMat N A - 1 := by
    simp [redMat, map_sub]
  constructor
  · intro h i j
    have h0 : redMat N (A - 1) = 0 := by rw [hmap, h, sub_self]
    have h2 := congrFun (congrFun h0 i) j
    rw [redMat_apply] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by simpa using h2)
  · intro h
    have h0 : redMat N (A - 1) = 0 := by
      ext i j
      rw [redMat_apply]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((A - 1) i j) N).mpr (h i j)
    rw [hmap] at h0
    exact sub_eq_zero.mp h0
