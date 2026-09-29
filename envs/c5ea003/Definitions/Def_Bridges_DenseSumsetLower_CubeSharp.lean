-- Prove2me | Definitions.Def_Bridges_DenseSumsetLower_CubeSharp
-- name    : Bridges_DenseSumsetLower_CubeSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:13.118343+00:00
-- url     : https://prove2.me/theorems/0c5a0ffb-30bc-4794-8cd7-cab7ab0cfcdb
-- title:
--   Aether Catalog definitions — Bridges_DenseSumsetLower_CubeSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.DenseSumsetLower.CubeSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/DenseSumsetLower/CubeSharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
/-
# The matching upper bound for affine cubes in `δ`-dense subsets of `[n]`

`Bridges.DenseSumsetLower.Cube` proves the *existence* side of the multi-fold problem:
every `S ⊆ [0,n)` with `|S| ≥ δ n` contains an affine cube
`u + {0,a₁} + ⋯ + {0,a_d}` of dimension `d` as soon as `(4/δ)^{2^d} ≤ 2 n`, i.e. for every
`d ≤ log₂ (log (2n) / log (4/δ))`.

This file proves the opposite (first-moment) side: for `d` slightly *above* that range
there are `δ`-dense sets `S ⊆ [n]` containing **no** affine cube of dimension `d` with
`2^d` distinct elements.  A `d`-dimensional cube inside `[n]` is described by `d + 1`
parameters — the base point `u` and the generators `a₁, …, a_d` — so the union bound costs
`n^{d+1}` while each proper cube forces `2^d` points of `S`; the two balance at
`2^d ≈ (d+1)·log n / log (1/δ)`, i.e. at `d ≈ log₂ (log n / log (1/δ))`, the same order as
the existence threshold.

Contents:
* `DenseSumsetLower.funCube` — the affine cube `u + {0,a₁} + ⋯ + {0,a_d}` in `ℕ`, written
  as the set of subset sums of the generator family `f : Fin d → ℕ`;
* `DenseSumsetLower.exists_card_eq_no_cube` — the counting statement: if
  `n^{d+1}·m^L < n^L` then some `m`-element `S ⊆ [n]` contains no `d`-dimensional cube with
  at least `L` distinct elements;
* `DenseSumsetLower.cube_pow_cond` — the analytic form of `n^c·m^L < n^L` for
  `m = ⌈δ n⌉`, valid for **all** exponents `c` (unlike `DeltaDense.pow_cond`, which is
  restricted to `c ≤ 10`; here `c = d + 1` must be allowed to grow with `n`);
* `DenseSumsetLower.exists_dense_no_cube` and its asymptotic packaging
  `DenseSumsetLower.eventually_exists_dense_no_cube`;
* `DenseSumsetLower.cube_dimension_window` — the consistency of the two sides: for `n`
  large no dimension `d` satisfies both the existence condition `(4/δ)^{2^d} ≤ 2n` of
  `exists_cube_of_density_int` and the avoidance condition
  `(1+ε)(d+1)·log n ≤ 2^d·log (1/δ)` proved here, so the avoidance range of `d` begins
  strictly beyond the existence range.

Caveat on the shape of the two bounds: the avoidance statement is about *proper* cubes
(those with `2^d` distinct elements — equivalently, `L = 2^d` in the counting form, which
also covers every intermediate `L`), whereas the existence statement of `Cube.lean`
produces a cube with nonzero generators which need not be proper.  Upgrading the existence
side to proper cubes is exactly sub-conjecture 3 of `FUTURE_DIRECTIONS.md`.
-/

namespace DenseSumsetLower

open Finset DeltaDense

/-! ## Affine cubes in `ℕ` as sets of subset sums -/

/-- `funCube u f` is the affine cube `u + {0, f 0} + ⋯ + {0, f (d-1)}`, realised as the set
of all subset sums `u + ∑_{i ∈ T} f i`, `T ⊆ {0, …, d-1}`. -/
def funCube {d : ℕ} (u : ℕ) (f : Fin d → ℕ) : Finset ℕ :=
  Finset.univ.image (fun T : Finset (Fin d) => u + ∑ i ∈ T, f i)




/-! ## The counting statement -/


/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no proper cube of a given dimension -/




end DenseSumsetLower


