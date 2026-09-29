-- Prove2me | Theorems.Thm_MultiPrime_density_le
-- name    : MultiPrime.density_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:34:19.525036+00:00
-- url     : https://prove2.me/theorems/cf243822-2953-4a1c-8b65-8bcc14d1a910
-- title:
--   Density bound.
-- statement:
--   **Density bound.**  At most a `∑ r_i / p_i` fraction of all residues are
--   successful.
--
--   ```lean
--   theorem MultiPrime.density_le(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) :
--       ((goodMulti R).card : ℝ) ≤ (∑ i, ((R i).card : ℝ) / P i) * ∏ i, (P i : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliMultiPrime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliMultiPrime.lean#L101

-- Thm stub generated from Geometry/SingularModuliMultiPrime.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliMultiPrime
/-
# Singular Moduli Factoring for Arbitrary Composites: it is a *smallest-factor*
# finder

Second research cycle, generalising `SingularModuliBarrier.lean` from semiprimes
`N = p q` to arbitrary squarefree composites `N = p₁ ⋯ p_k`.

Chinese Remainder coordinates now live in `∀ i, ZMod (p i)`, and an evaluation
point `j₀` produces a nontrivial gcd exactly when the reduction of `j₀` is a
root of the class polynomial modulo *some but not all* of the primes.  We prove:

* `MultiPrime.card_goodMulti` — the exact partition identity
  `|G| + ∏ r_i + ∏ (p_i - r_i) = ∏ p_i`;
* `MultiPrime.density_le` — the success density is at most `∑ r_i / p_i`
  (a Weierstrass product inequality, proved here from scratch);
* `MultiPrime.expectedTrialsMulti_ge` — hence the expected number of
  evaluations is at least `p_min / (k d)`, where `d` bounds the number of roots
  of the class polynomial modulo each prime and `p_min` is the *smallest* prime
  factor.

Interpretation.  The `√N` bound for balanced semiprimes is not a coincidence of
the two-prime case: singular moduli factoring is intrinsically a **smallest
prime factor** finder, of the same shape as Pollard rho (`Θ(√p_min)` — better in
the exponent) and Pollard `p-1`.  For balanced semiprimes `p_min ≈ √N` and one
recovers the barrier; for an unbalanced `N` with a small factor the method is
fast for exactly the same, uninteresting, reason that trial division is.

Everything is stated for arbitrary root sets `R i ⊆ ZMod (p i)`; no unproved
property of Hilbert class polynomials is used.
-/

open MultiPrime

open Finset

variable {k : ℕ} {P : Fin k → ℕ} [∀ i, NeZero (P i)]

theorem MultiPrime.density_le(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) :
    ((goodMulti R).card : ℝ) ≤ (∑ i, ((R i).card : ℝ) / P i) * ∏ i, (P i : ℝ) := by sorry
