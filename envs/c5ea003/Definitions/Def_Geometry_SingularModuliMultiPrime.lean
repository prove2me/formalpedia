-- Prove2me | Definitions.Def_Geometry_SingularModuliMultiPrime
-- name    : Geometry_SingularModuliMultiPrime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:46.630856+00:00
-- url     : https://prove2.me/theorems/b3caebaf-bd5d-4249-b101-ad72ed0b6013
-- title:
--   Aether Catalog definitions — Geometry_SingularModuliMultiPrime
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SingularModuliMultiPrime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SingularModuliMultiPrime.lean by skeleton subtraction
import Mathlib
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

namespace MultiPrime

open Finset

variable {k : ℕ} {P : Fin k → ℕ} [∀ i, NeZero (P i)]

/-- Successful evaluation points for a composite with `k` prime factors, in CRT
coordinates: those lying in the structured set modulo some, but not all, of the
primes. -/
def goodMulti (R : ∀ i, Finset (ZMod (P i))) : Finset (∀ i, ZMod (P i)) :=
  Finset.univ.filter fun x => (∃ i, x i ∈ R i) ∧ (∃ i, x i ∉ R i)




/-- Expected number of evaluation points for a composite with `k` prime
factors. -/
noncomputable def expectedTrialsMulti (R : ∀ i, Finset (ZMod (P i))) : ℝ :=
  (∏ i, (P i : ℝ)) / (goodMulti R).card


end MultiPrime


