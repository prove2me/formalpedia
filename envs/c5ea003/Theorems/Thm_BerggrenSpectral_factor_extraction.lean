-- Prove2me | Theorems.Thm_BerggrenSpectral_factor_extraction
-- name    : BerggrenSpectral.factor_extraction
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:37:02.873269+00:00
-- url     : https://prove2.me/theorems/cadbabc1-2f5a-424f-9b8c-f5c09de5348f
-- title:
--   Factor extraction.
-- statement:
--   **Factor extraction.**  If `p` divides `x` but `q` does not, then `gcd (x, p q) = p`.
--
--   ```lean
--   theorem BerggrenSpectral.factor_extraction(p q : ℕ) (hq : q.Prime) (x : ℤ)
--       (hpx : (p : ℤ) ∣ x) (hqx : ¬ (q : ℤ) ∣ x) (hp0 : p ≠ 0) :
--       Int.gcd x ((p * q : ℕ) : ℤ) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenSpectral/Factorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenSpectral/Factorization.lean#L55

-- Thm stub generated from Cryptography/BerggrenSpectral/Factorization.lean
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

theorem BerggrenSpectral.factor_extraction(p q : ℕ) (hq : q.Prime) (x : ℤ)
    (hpx : (p : ℤ) ∣ x) (hqx : ¬ (q : ℤ) ∣ x) (hp0 : p ≠ 0) :
    Int.gcd x ((p * q : ℕ) : ℤ) = p := by sorry
