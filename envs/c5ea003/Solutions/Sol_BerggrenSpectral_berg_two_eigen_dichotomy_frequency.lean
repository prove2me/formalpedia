-- Prove2me | solution 1 for BerggrenSpectral.berg_two_eigen_dichotomy_frequency
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:02:07.397975+00:00
-- url     : https://prove2.me/submissions/645c9631-4220-48b6-9452-170d99e2b7ef

-- Sol generated from Cryptography/BerggrenSpectral/EigenvaluesModP.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_LorentzAndTree
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_berg_two_resonance_nqr
import Theorems.Thm_BerggrenSpectral_berg_two_resonance_qr
import Theorems.Thm_BerggrenSpectral_two_chi_cases
import Theorems.Thm_BerggrenSpectral_two_ne_zero_of_odd_prime

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




/-- The hyperbolic quadratic has a root mod `p` iff `2` is a square mod `p`. -/
theorem berg_two_quadratic_root_iff_isSquare_two (hp : p ≠ 2) :
    (∃ lam : ZMod p, lam ^ 2 - 6 * lam + 1 = 0) ↔ IsSquare (2 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_prime p hp
  constructor
  · rintro ⟨lam, hlam⟩
    refine ⟨(lam - 3) * (2 : ZMod p)⁻¹, ?_⟩
    field_simp
    linear_combination -hlam
  · rintro ⟨s, hs⟩
    exact ⟨3 + 2 * s, by linear_combination (4 : ZMod p) * hs.symm⟩






open BerggrenSpectral in
theorem solution(hp : p ≠ 2) :
    ((∃ lam : ZMod p, lam ≠ -1 ∧ (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0) →
        (redMat p M₂) ^ (p - 1) = 1) ∧
    ((∀ lam : ZMod p, (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 → lam = -1) →
        (redMat p M₂) ^ (p + 1) = 1) := by
  have hne : (2 : ZMod p) ≠ 0 := two_ne_zero_of_odd_prime p hp
  have hhalf : p / 2 = (p - 1) / 2 := by
    obtain ⟨t, ht⟩ := (Nat.Prime.odd_of_ne_two Fact.out hp); omega
  constructor
  · rintro ⟨lam, hne1, hroot⟩
    have hquad : lam ^ 2 - 6 * lam + 1 = 0 := by
      rcases mul_eq_zero.mp hroot with h1 | h1
      · exact absurd (by linear_combination h1 : lam = -1) hne1
      · exact h1
    have hsq : IsSquare (2 : ZMod p) :=
      (berg_two_quadratic_root_iff_isSquare_two p hp).mp ⟨lam, hquad⟩
    have hchi := (ZMod.euler_criterion p hne).mp hsq
    rw [hhalf] at hchi
    exact berg_two_resonance_qr p hp hchi
  · intro honly
    have hnsq : ¬ IsSquare (2 : ZMod p) := by
      intro hs
      obtain ⟨lam, hlam⟩ := (berg_two_quadratic_root_iff_isSquare_two p hp).mpr hs
      have hlam1 : lam = -1 := honly lam (by rw [hlam, mul_zero])
      rw [hlam1] at hlam
      have hcube : (2 : ZMod p) ^ 3 = 0 := by linear_combination hlam
      exact hne (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube)
    have hchi : (2 : ZMod p) ^ ((p - 1) / 2) = -1 := by
      rcases two_chi_cases p hp with h | h
      · exact absurd ((ZMod.euler_criterion p hne).mpr (by rw [hhalf]; exact h)) hnsq
      · exact h
    exact berg_two_resonance_nqr p hp hchi
