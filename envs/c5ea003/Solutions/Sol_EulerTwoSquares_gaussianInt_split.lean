-- Prove2me | solution 1 for EulerTwoSquares.gaussianInt_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:42:18.087948+00:00
-- url     : https://prove2.me/submissions/f5ab4b36-b5b4-478d-b102-4e8067282ebc

-- Sol generated from Algebra/EulerTwoSquaresGaussian.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_gaussianInt_dvd_iff_cross

/-!
# The class bit is a Gaussian divisibility, and the two bits split `N` in `ℤ[i]`

The counting theorem of `EulerTwoSquaresCount` attaches to every representation
`a² + b² = p*q` a pair of bits

`(⟦p ∣ a*f - b*e⟧, ⟦q ∣ a*h - b*g⟧) ∈ Bool × Bool`,

where `p = e²+f²` and `q = g²+h²`.  That bit looks like an ad-hoc congruence.  This file
identifies it with a statement in the Gaussian integers `ℤ[i] = GaussianInt`:

`EulerTwoSquares.gaussianInt_dvd_iff_cross`:  `⟨e,f⟩ ∣ ⟨a,b⟩  ↔  (p : ℤ) ∣ a*f - b*e`.

So the bit records **which of the two conjugate Gaussian primes above `p` divides `a + b·i`**
— a Frobenius-style choice — and `EulerTwoSquares.gaussianInt_dvd_exactly_one` says exactly
one of `⟨e,f⟩`, `⟨e,-f⟩` does.  Finally `EulerTwoSquares.gaussianInt_split` exhibits the
resulting factorisation of `a + b·i` into a Gaussian prime above `p` and a Gaussian integer of
norm `q`, which is the structural reason the representation count is a power of two.

Everything here is elementary: the only inputs from `EulerTwoSquaresCount` are
`prime_dvd_cross_or` and `prime_not_dvd_cross_both`.
-/

open EulerTwoSquares

variable {p q : ℕ}


/-! ## From one divisibility to the other -/



/-! ## The bridge -/



/-! ## Exactly one Gaussian prime above `p` divides a given representation -/




open EulerTwoSquares in
theorem solution(hp : p.Prime) {e f a b : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q)
    (hdvd : (p : ℤ) ∣ a * f - b * e) :
    ∃ w : GaussianInt, (⟨a, b⟩ : GaussianInt) = ⟨e, f⟩ * w ∧ Zsqrtd.norm w = (q : ℤ) := by
  obtain ⟨w, hw⟩ := (gaussianInt_dvd_iff_cross (q := q) hp hef hab).2 hdvd
  refine ⟨w, hw, ?_⟩
  have hnorm : Zsqrtd.norm (⟨a, b⟩ : GaussianInt) =
      Zsqrtd.norm (⟨e, f⟩ : GaussianInt) * Zsqrtd.norm w := by
    rw [hw, Zsqrtd.norm_mul]
  have hab' : Zsqrtd.norm (⟨a, b⟩ : GaussianInt) = (p : ℤ) * q := by
    simp only [Zsqrtd.norm_def]; linear_combination hab
  have hef' : Zsqrtd.norm (⟨e, f⟩ : GaussianInt) = (p : ℤ) := by
    simp only [Zsqrtd.norm_def]; linear_combination hef
  rw [hab', hef'] at hnorm
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero
  exact (mul_left_cancel₀ hp0 hnorm).symm
