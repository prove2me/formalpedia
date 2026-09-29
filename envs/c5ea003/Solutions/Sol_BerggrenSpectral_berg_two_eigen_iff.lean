-- Prove2me | solution 1 for BerggrenSpectral.berg_two_eigen_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:02:08.380089+00:00
-- url     : https://prove2.me/submissions/0596a4e7-a7a9-48c4-a036-025b8297a37c

-- Sol generated from Cryptography/BerggrenSpectral/EigenvaluesModP.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_HyperbolicResonance
import Definitions.Def_Cryptography_BerggrenSpectral_LorentzAndTree

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

/-- The determinant of `M₂ - λ` in closed form. -/
theorem det_M2R_sub (R : Type*) [CommRing R] (lam : R) :
    (M2R R - lam • 1).det = -((lam + 1) * (lam ^ 2 - 6 * lam + 1)) := by
  rw [Matrix.det_fin_three]
  simp [M2R]
  ring









open BerggrenSpectral in
theorem solution(lam : ZMod p) :
    (∃ v : Fin 3 → ZMod p, v ≠ 0 ∧ M2R (ZMod p) *ᵥ v = lam • v) ↔
      (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 := by
  have hkey : (∃ v : Fin 3 → ZMod p, v ≠ 0 ∧ (M2R (ZMod p) - lam • 1) *ᵥ v = 0) ↔
      (M2R (ZMod p) - lam • 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff
  rw [det_M2R_sub, neg_eq_zero] at hkey
  rw [← hkey]
  constructor
  · rintro ⟨v, hv, hvec⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hvec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  · rintro ⟨v, hv, hvec⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hvec
    exact sub_eq_zero.mp hvec
