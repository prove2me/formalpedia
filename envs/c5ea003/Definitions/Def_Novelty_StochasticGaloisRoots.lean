-- Prove2me | Definitions.Def_Novelty_StochasticGaloisRoots
-- name    : Novelty_StochasticGaloisRoots
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:50.461776+00:00
-- url     : https://prove2.me/theorems/506f0547-21d0-4a69-8de9-a1a1d5e1de0c
-- title:
--   Aether Catalog definitions — Novelty_StochasticGaloisRoots
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StochasticGaloisRoots`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StochasticGaloisRoots.lean by skeleton subtraction
import Mathlib
/-
# Stochastic Galois Theory over Finite Fields: the Expected-Roots Identity

This file establishes the cleanest instance of the "random polynomial behaves like a
random permutation" correspondence over a finite field (indeed, over any finite
commutative ring).

A monic polynomial of degree `n` over `K` is encoded by its coefficient vector
`v : Fin n → K`, standing for `X^n + ∑ i, v i • X^i`.  Its *roots* in `K` are the
`r : K` with `monicEval n v r = 0`; these correspond exactly to the *linear factors*
of the polynomial, i.e. to the *fixed points* of the associated Frobenius permutation.

The main theorem `total_root_incidences` says that, summed over all `q^n` monic
polynomials of degree `n ≥ 1`, the total number of (polynomial, root) incidences is
exactly `q^n`.  Dividing by the number of polynomials, the **expected number of roots
of a uniformly random monic degree-`n` polynomial is exactly `1`** — matching the
classical fact that a uniformly random permutation in `S_n` has, on average, exactly
one fixed point.  This is the finite-field shadow of the random-permutation model of
Galois groups.
-/

open Finset BigOperators

namespace StochasticGalois

variable {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]

/-- The value at `r` of the monic degree-`n` polynomial `X^n + ∑ i, (v i)•X^i`
whose non-leading coefficients are given by `v : Fin n → K`. -/
def monicEval (n : ℕ) (v : Fin n → K) (r : K) : K :=
  r ^ n + ∑ i : Fin n, v i * r ^ (i : ℕ)

/-
**Fiber count.** For a fixed base point `r`, the number of monic polynomials of
degree `m + 1` having `r` as a root is `q^m` (where `q = |K|`): the constant coefficient
`v 0` is forced by the remaining coefficients, so the solution set is a graph over
`Fin m → K`.
-/

/-
**Total (polynomial, root) incidences.** For `n ≥ 1`, summing the number of roots
over all `q^n` monic degree-`n` polynomials gives exactly `q^n`.  Equivalently, the
expected number of roots of a uniformly random monic degree-`n` polynomial over a
finite commutative ring is exactly `1`.
-/


end StochasticGalois


