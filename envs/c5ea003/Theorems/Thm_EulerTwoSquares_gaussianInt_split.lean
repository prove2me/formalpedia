-- Prove2me | Theorems.Thm_EulerTwoSquares_gaussianInt_split
-- name    : EulerTwoSquares.gaussianInt_split
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:46:09.477781+00:00
-- url     : https://prove2.me/theorems/cb881e4a-2513-436e-8bcb-659f2fa47f89
-- title:
--   The Gaussian splitting behind the count.
-- statement:
--   **The Gaussian splitting behind the count.**  A representation of `p*q` whose `p`-bit is
--   set factors in `ℤ[i]` as the Gaussian prime `e + f·i` above `p` times a Gaussian integer of
--   norm `q`; the two choices of conjugate are exactly the two class bits.
--
--   ```lean
--   theorem EulerTwoSquares.gaussianInt_split(hp : p.Prime) {e f a b : ℤ}
--       (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q)
--       (hdvd : (p : ℤ) ∣ a * f - b * e) :
--       ∃ w : GaussianInt, (⟨a, b⟩ : GaussianInt) = ⟨e, f⟩ * w ∧ Zsqrtd.norm w = (q : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresGaussian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresGaussian.lean#L121

-- Thm stub generated from Algebra/EulerTwoSquaresGaussian.lean
import Mathlib

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


variable {p q : ℕ}


/-! ## From one divisibility to the other -/



/-! ## The bridge -/



/-! ## Exactly one Gaussian prime above `p` divides a given representation -/

theorem EulerTwoSquares.gaussianInt_split(hp : p.Prime) {e f a b : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q)
    (hdvd : (p : ℤ) ∣ a * f - b * e) :
    ∃ w : GaussianInt, (⟨a, b⟩ : GaussianInt) = ⟨e, f⟩ * w ∧ Zsqrtd.norm w = (q : ℤ) := by sorry
