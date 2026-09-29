-- Prove2me | Definitions.Def_Shared_GilbertLatticeSumTwoSquares
-- name    : Shared_GilbertLatticeSumTwoSquares
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:01:12.009476+00:00
-- url     : https://prove2.me/theorems/b486d8dc-9aac-40b2-8b0c-f1f42b3dadcd
-- title:
--   Aether Catalog definitions — Shared_GilbertLatticeSumTwoSquares
-- statement:
--   Definition bundle for the Aether Catalog module Shared.GilbertLatticeSumTwoSquares, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/GilbertLatticeSumTwoSquares.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2

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

namespace GilbertLattice

/-! ## Aligned configurations -/

/-- The *aligned* configuration with offset `(s,t)`: every point is placed at the same
position inside its cell, so the point set is the translated lattice `ℤ² + (s,t)`. -/
noncomputable def alignedConfig {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : Config where
  off := fun _ => (s, t)
  off_nonneg_fst := fun _ => hs0
  off_nonneg_snd := fun _ => ht0
  off_le_one_fst := fun _ => hs1
  off_le_one_snd := fun _ => ht1

variable {s t : ℝ} {hs0 : 0 ≤ s} {hs1 : s ≤ 1} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}




/-! ## The spectrum of squared edge lengths -/

/-- The **spectrum** of the aligned family: the set of integers that occur as the squared
distance between the points of two distinct cells of an aligned configuration. -/
def latticeSpectrum : Set ℕ :=
  {n : ℕ | ∃ c c' : ℤ × ℤ, c ≠ c' ∧ (c.1 - c'.1) ^ 2 + (c.2 - c'.2) ^ 2 = (n : ℤ)}









/-! ## Geometric consequences -/




/-! ## The critical radius of the aligned subfamily -/




end GilbertLattice


