-- Prove2me | solution 1 for BerggrenSpectral.berg_resonance_crt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:59:57.416055+00:00
-- url     : https://prove2.me/submissions/6e5dc44a-d8c5-4fff-9ec1-7f328de08ebb

-- Sol generated from Cryptography/BerggrenSpectral/SpectrumAndTrace.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_Generators
import Definitions.Def_Cryptography_BerggrenSpectral_SpectrumAndTrace
import Definitions.Def_Cryptography_BerggrenSpectral_UnipotentResonance
import Theorems.Thm_BerggrenSpectral_redMat_eq_one_iff
import Theorems.Thm_BerggrenSpectral_redMat_pow

/-!
# The Exact Resonance Spectrum and the Berggren–Lucas Trace Sequence

Second research cycle.  Where `HyperbolicResonance.lean` produced *sufficient* resonant
frequencies, this file determines the resonance set **exactly**, decomposes it across the
factors of a semiprime modulus, and extracts an arithmetic sequence — the *Berggren–Lucas
trace sequence* — carrying a Fermat-type congruence.

## Main results

* `berg_two_pow_eq_one_iff` : modulo an odd prime `p`,
  `M₂ ^ k ≡ 1 ⟺ U ^ k = 1 ∧ k even`, where `U = !![3,2;4,3]` is the hyperbolic block.
  This is an exact description of the resonance spectrum, not merely a divisibility bound.
* `berg_two_orderOf` : `ord_p(M₂) = lcm (2, ord_p(U))`.
* `berg_resonance_crt` : for coprime moduli the resonance sets intersect,
  `M₂ ^ k ≡ 1 (mod m n) ⟺ M₂ ^ k ≡ 1 (mod m) ∧ M₂ ^ k ≡ 1 (mod n)`.  Factoring `N = p q`
  is therefore exactly the problem of *separating two resonant frequencies inside one
  modulus*, which is the conceptual content of `Factorization.lean`.
* `berg_trace_rec`, `berg_trace_values` : the traces `t k = tr (M₂ ^ k)` satisfy the
  Newton recurrence `t (k+3) = 5 t (k+2) + 5 t (k+1) - t k` of the characteristic
  polynomial, with `t 0, t 1, t 2, t 3 = 3, 5, 35, 197`.
* `berg_trace_fermat` : for every odd prime `p`, `t p ≡ 5 (mod p)` — a Fermat/Lucas-type
  congruence for the Berggren tree, proved from the matrix Frobenius, *not* from a
  hypothetical eigenvalue computation.
* `berg_trace_composite_witness` : the contrapositive is a compositeness test;
  `berg_nine_composite_witness` runs it on `N = 9`.
-/

open BerggrenSpectral

open Matrix

variable (p : ℕ) [Fact p.Prime]

/-! ## The exact resonance spectrum modulo a prime -/



/-! ## Resonance across a composite modulus -/


/-! ## The Berggren–Lucas trace sequence -/












open BerggrenSpectral in
theorem solution(m n k : ℕ) (h : Nat.Coprime m n) :
    (redMat (m * n) M₂) ^ k = 1 ↔ (redMat m M₂) ^ k = 1 ∧ (redMat n M₂) ^ k = 1 := by
  have hco : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  rw [← redMat_pow, ← redMat_pow, ← redMat_pow, redMat_eq_one_iff, redMat_eq_one_iff,
    redMat_eq_one_iff]
  constructor
  · intro hall
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact dvd_trans ⟨(n : ℤ), by push_cast; ring⟩ (hall i j)
    · exact dvd_trans ⟨(m : ℤ), by push_cast; ring⟩ (hall i j)
  · rintro ⟨h1, h2⟩ i j
    have := hco.mul_dvd (h1 i j) (h2 i j)
    simpa [Nat.cast_mul] using this
