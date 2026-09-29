-- Prove2me | solution 1 for DenseSumsetLower.exists_dense_no_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:33:24.738128+00:00
-- url     : https://prove2.me/submissions/f5382fef-7ea4-45d0-b9a4-c491eff56bd8

-- Sol generated from Bridges/DenseSumsetLower/CubeSharp.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Definitions.Def_Bridges_DenseSumsetLower_CubeSharp
import Theorems.Thm_DenseSumsetLower_cube_pow_cond
import Theorems.Thm_DenseSumsetLower_exists_card_eq_no_cube
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

open DenseSumsetLower

open Finset DeltaDense

/-! ## Affine cubes in `ℕ` as sets of subset sums -/





/-! ## The counting statement -/


/-! ## The analytic form of the counting condition -/


/-! ## Dense sets with no proper cube of a given dimension -/





open DenseSumsetLower in
theorem solution{δ : ℝ} (h0 : 0 < δ) {n d : ℕ} (hn2 : 2 ≤ n)
    (hδn : δ * n ≤ n)
    (hcond : ((d : ℝ) + 1) * Real.log n < (2 ^ d : ℕ) * Real.log (1 / (δ + 1 / n))) :
    ∃ S ⊆ range n, δ * n ≤ S.card ∧
      ∀ (u : ℕ) (f : Fin d → ℕ), (∀ i, 0 < f i) → (funCube u f).card = 2 ^ d →
        ¬ (funCube u f ⊆ S) := by
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hmn : ⌈δ * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.2 hδn
  have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
  have hcond' : n ^ (d + 1) * (⌈δ * (n : ℝ)⌉₊) ^ (2 ^ d) < n ^ (2 ^ d) := by
    refine cube_pow_cond h0 (by omega) ?_
    rw [hcast]
    exact_mod_cast hcond
  obtain ⟨S, hSsub, hScard, hSno⟩ :=
    exists_card_eq_no_cube hmn (Nat.one_le_two_pow) hcond'
  refine ⟨S, hSsub, by rw [hScard]; exact Nat.le_ceil _, ?_⟩
  intro u f hf hcard
  exact hSno u f hf (le_of_eq hcard.symm)
