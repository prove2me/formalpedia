-- Prove2me | solution 1 for BerggrenSpectral.factor_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:03:45.641478+00:00
-- url     : https://prove2.me/submissions/b2fafe62-c7dc-4e36-89bb-c6b9663c1abe

-- Sol generated from Cryptography/BerggrenSpectral/Factorization.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance

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
theorem solution(p q : ℕ) (hq : q.Prime) (x : ℤ)
    (hpx : (p : ℤ) ∣ x) (hqx : ¬ (q : ℤ) ∣ x) (hp0 : p ≠ 0) :
    Int.gcd x ((p * q : ℕ) : ℤ) = p := by
  set g := Int.gcd x ((p * q : ℕ) : ℤ) with hg
  have hgx : (g : ℤ) ∣ x := Int.gcd_dvd_left _ _
  have hgN : g ∣ p * q := by exact_mod_cast Int.gcd_dvd_right x ((p * q : ℕ) : ℤ)
  have hpg : p ∣ g := by
    have h2 : (p : ℤ) ∣ ((p * q : ℕ) : ℤ) := by push_cast; exact Dvd.intro q rfl
    exact Int.dvd_gcd hpx h2
  obtain ⟨t, ht⟩ := hpg
  have htq : t ∣ q := (mul_dvd_mul_iff_left hp0).mp (ht ▸ hgN)
  rcases hq.eq_one_or_self_of_dvd t htq with h1 | h1
  · rw [ht, h1, mul_one]
  · exact absurd (((show (q : ℤ) ∣ (g : ℤ) by rw [ht, h1]; exact ⟨(p : ℤ), by push_cast; ring⟩)).trans
      hgx) hqx
