-- Prove2me | Theorems.Thm_BerggrenSpectral_berg_two_eigen_dichotomy_frequency
-- name    : BerggrenSpectral.berg_two_eigen_dichotomy_frequency
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:36:40.972225+00:00
-- url     : https://prove2.me/theorems/0d3a209d-a9d4-493d-a232-a96b726c7d54
-- title:
--   Spectrum ⇒ frequency.
-- statement:
--   **Spectrum ⇒ frequency.**  The split/inert dichotomy of the spectrum mod `p` is exactly
--   the dichotomy of resonant frequencies.
--
--   ```lean
--   theorem BerggrenSpectral.berg_two_eigen_dichotomy_frequency(hp : p ≠ 2) :
--       ((∃ lam : ZMod p, lam ≠ -1 ∧ (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0) →
--           (redMat p M₂) ^ (p - 1) = 1) ∧
--       ((∀ lam : ZMod p, (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 → lam = -1) →
--           (redMat p M₂) ^ (p + 1) = 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenSpectral/EigenvaluesModP.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenSpectral/EigenvaluesModP.lean#L101

-- Thm stub generated from Cryptography/BerggrenSpectral/EigenvaluesModP.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_LorentzAndTree
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance

/-!
# The Exact Eigenvalue Distribution of `M₂` mod `p`

Fourth research cycle: the *spectral distribution* itself, modulo a prime.  Over `ℤ` the
generator `M₂` has spectrum `{-1, 3 + 2√2, 3 - 2√2}` (`berg_charpoly_two`).  Modulo an odd
prime `p` the two hyperbolic eigenvalues become *visible in `𝔽_p` exactly when `2` is a
quadratic residue*, i.e. exactly when `p ≡ ±1 (mod 8)`.

## Main results

* `berg_two_eigen_iff` : `λ` is an eigenvalue of `M₂` over `ZMod p` (there is a nonzero
  vector with `M₂ v = λ v`) **iff** `(λ + 1) (λ² - 6λ + 1) = 0`.
* `berg_two_quadratic_root_iff_isSquare_two` : the quadratic factor has a root in `ZMod p`
  iff `2` is a square mod `p`.
* `berg_two_eigen_split` : for `p ≡ ±1 (mod 8)` the two hyperbolic eigenvalues `3 ± 2√2`
  exist in `𝔽_p`, are distinct, and differ from `-1`; the spectrum is a full set of three
  eigenvalues.
* `berg_two_eigen_inert` : for `p ≡ ±3 (mod 8)` the only eigenvalue is `-1`; the hyperbolic
  part is inert, living in `𝔽_{p²}`.
* `berg_two_eigen_dichotomy_frequency` : the split/inert dichotomy is precisely the
  dichotomy of resonant frequencies `p - 1` vs `p + 1` of `HyperbolicResonance.lean`.
  This is the sense in which "the resonant frequency is read off the spectrum mod `p`".
* `berg_semiprime_frequency_misalignment` : if `p ≡ ±1` and `q ≡ ±3 (mod 8)` then the two
  primes of `N = p q` carry *different* spectral behaviour — split versus inert — which is
  the structural source of the resonance misalignment exploited in `Factorization.lean`.
-/

open BerggrenSpectral

open Matrix

variable (p : ℕ) [Fact p.Prime]

theorem BerggrenSpectral.berg_two_eigen_dichotomy_frequency(hp : p ≠ 2) :
    ((∃ lam : ZMod p, lam ≠ -1 ∧ (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0) →
        (redMat p M₂) ^ (p - 1) = 1) ∧
    ((∀ lam : ZMod p, (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 → lam = -1) →
        (redMat p M₂) ^ (p + 1) = 1) := by sorry
