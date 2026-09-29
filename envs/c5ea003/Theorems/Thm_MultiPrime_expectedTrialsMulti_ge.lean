-- Prove2me | Theorems.Thm_MultiPrime_expectedTrialsMulti_ge
-- name    : MultiPrime.expectedTrialsMulti_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:34:12.915015+00:00
-- url     : https://prove2.me/theorems/cc8c641a-5370-4cff-a156-547e64477cbb
-- title:
--   The barrier is governed by the smallest prime factor.
-- statement:
--   **The barrier is governed by the smallest prime factor.**  If the class
--   polynomial has at most `d` roots modulo each prime and every prime is at least
--   `pmin`, the expected number of evaluations is at least `pmin / (k d)`.  For a
--   balanced semiprime this is the `√N` barrier; in general the method is a
--   smallest-factor finder.
--
--   ```lean
--   theorem MultiPrime.expectedTrialsMulti_ge(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) (d pmin : ℕ)
--       (hd : 0 < d) (hdR : ∀ i, (R i).card ≤ d) (hpmin : ∀ i, pmin ≤ P i)
--       (hG : 0 < (goodMulti R).card) :
--       (pmin : ℝ) / (k * d) ≤ expectedTrialsMulti R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliMultiPrime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliMultiPrime.lean#L154

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

theorem MultiPrime.expectedTrialsMulti_ge(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) (d pmin : ℕ)
    (hd : 0 < d) (hdR : ∀ i, (R i).card ≤ d) (hpmin : ∀ i, pmin ≤ P i)
    (hG : 0 < (goodMulti R).card) :
    (pmin : ℝ) / (k * d) ≤ expectedTrialsMulti R := by sorry
