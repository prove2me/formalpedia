-- Prove2me | Theorems.Thm_StochasticGalois_card_roots_fiber
-- name    : StochasticGalois.card_roots_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:37:12.601745+00:00
-- url     : https://prove2.me/theorems/695b138b-855a-4e5f-b3f9-46f22a9a6a54
-- title:
--   Card roots fiber
-- statement:
--   Formal statement of `StochasticGalois.card_roots_fiber` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem StochasticGalois.card_roots_fiber(m : ℕ) (r : K) :
--       (Finset.univ.filter (fun v : Fin (m + 1) → K => monicEval (m + 1) v r = 0)).card
--         = (Fintype.card K) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StochasticGaloisRoots.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StochasticGaloisRoots.lean#L39

-- Thm stub generated from Novelty/StochasticGaloisRoots.lean
import Mathlib
import Definitions.Def_Novelty_StochasticGaloisRoots
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

open StochasticGalois

variable {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]


/-
**Fiber count.** For a fixed base point `r`, the number of monic polynomials of
degree `m + 1` having `r` as a root is `q^m` (where `q = |K|`): the constant coefficient
`v 0` is forced by the remaining coefficients, so the solution set is a graph over
`Fin m → K`.
-/

theorem StochasticGalois.card_roots_fiber(m : ℕ) (r : K) :
    (Finset.univ.filter (fun v : Fin (m + 1) → K => monicEval (m + 1) v r = 0)).card
      = (Fintype.card K) ^ m := by sorry
