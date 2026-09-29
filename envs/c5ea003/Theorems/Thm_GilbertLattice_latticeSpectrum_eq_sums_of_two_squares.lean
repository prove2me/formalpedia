-- Prove2me | Theorems.Thm_GilbertLattice_latticeSpectrum_eq_sums_of_two_squares
-- name    : GilbertLattice.latticeSpectrum_eq_sums_of_two_squares
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:37:42.150983+00:00
-- url     : https://prove2.me/theorems/54bf0e0f-339e-4140-b59e-ac592c286b94
-- title:
--   The spectrum is exactly the set of positive sums of two squares.
-- statement:
--   **The spectrum is exactly the set of positive sums of two squares.**
--
--   ```lean
--   theorem GilbertLattice.latticeSpectrum_eq_sums_of_two_squares:
--       latticeSpectrum = {n : ℕ | 0 < n ∧ ∃ x y : ℕ, n = x ^ 2 + y ^ 2} := by sorry
--
--
--
--
--
--
--   /-! ## Geometric consequences -/
--
--
--
--
--   /-! ## The critical radius of the aligned subfamily -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeSumTwoSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeSumTwoSquares.lean#L124

-- Thm stub generated from Shared/GilbertLatticeSumTwoSquares.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeSumTwoSquares

/-!
# A bridge: the conditioned Gilbert model and the two-square theorem

This file connects two areas that look unrelated at first sight:

* **continuum percolation on the square lattice** — Gilbert's disc model conditioned on
  `ℤ²`, where one point is placed in each cell of the grid and two points are joined
  when they are at distance `< R` (the model of `GilbertLatticeBasic.lean`), and
* **the arithmetic of sums of two squares** — Fermat's two-square theorem, the
  Brahmagupta–Fibonacci identity and the classification of the integers represented by
  the norm form `x² + y²` of the Gaussian integers.

The link is the family of *aligned* configurations, in which every point receives the
same offset `(s,t)` inside its cell: the point set is then a translate of `ℤ²`, so the
squared length of every edge of the Gilbert graph is an integer of the form `a² + b²`,
and conversely every such integer is realised.

## Main results

* `GilbertLattice.latticeSpectrum_eq_sums_of_two_squares` — the *spectrum* of the model
  (the set of squared edge lengths available to an aligned configuration) is exactly the
  set of positive sums of two squares;
* `GilbertLattice.prime_mem_latticeSpectrum_iff` — a prime `p` occurs as a squared edge
  length iff `p % 4 ≠ 3` (**Fermat's two-square theorem** read geometrically);
* `GilbertLattice.latticeSpectrum_iff_factorization` — the full arithmetic description:
  `n` occurs iff `n > 0` and every prime `q ≡ 3 [MOD 4]` divides `n` to an even power;
* `GilbertLattice.latticeSpectrum_mul` — the spectrum is closed under multiplication
  (Brahmagupta–Fibonacci: the geometry of the model is a *multiplicative monoid*);
* `GilbertLattice.exists_edge_of_length_sqrt_prime` — geometric form of the two-square
  theorem: for a prime `p` with `p % 4 ≠ 3` and any radius `R > √p`, the Gilbert graph
  of an aligned configuration contains an edge of length exactly `√p`, whereas for
  `p % 4 = 3` no edge of any aligned configuration has length `√p`;
* `GilbertLattice.alignedConfig_connected_iff` — an aligned configuration percolates (in
  fact is connected) exactly when `R > 1`, so `1` is the critical radius of the aligned
  subfamily, to be compared with `R_min ∈ [1/3, 1/2]` and `R_full = √5`;
* `GilbertLattice.neighborSet_alignedConfig` — for `1 < R ≤ √2` the neighbours of a cell
  are its four grid neighbours, the first instance of the Gauss circle problem.
-/

open GilbertLattice

/-! ## Aligned configurations -/


variable {s t : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}




/-! ## The spectrum of squared edge lengths -/

theorem GilbertLattice.latticeSpectrum_eq_sums_of_two_squares:
    latticeSpectrum = {n : ℕ | 0 < n ∧ ∃ x y : ℕ, n = x ^ 2 + y ^ 2} := by sorry
