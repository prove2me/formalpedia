-- Prove2me | solution 1 for DenseSumsetLower.cube_pow_cond
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:50.451493+00:00
-- url     : https://prove2.me/submissions/fc7da447-4f05-4dce-aab0-2704e70e6b56

-- Sol generated from Bridges/DenseSumsetLower/CubeSharp.lean
import Mathlib
import Definitions.Def_Bridges_DeltaDenseSumsetAvoidance
import Definitions.Def_Bridges_DenseSumsetLower_CubeSharp
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
theorem solution{δ : ℝ} (h0 : 0 < δ) {n c L : ℕ} (hn : 0 < n)
    (hcond : (c : ℝ) * Real.log n < L * Real.log (1 / (δ + 1 / n))) :
    n ^ c * (⌈δ * (n : ℝ)⌉₊) ^ L < n ^ L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hepos : 0 < δ + 1 / (n : ℝ) := by positivity
  -- `m ≤ (δ + 1/n) * n`
  have hm : (⌈δ * (n : ℝ)⌉₊ : ℝ) ≤ (δ + 1 / (n : ℝ)) * n := by
    have h1 : δ * (n : ℝ) + 1 = (δ + 1 / (n : ℝ)) * n := by
      field_simp
    refine le_trans (le_of_lt (Nat.ceil_lt_add_one (by positivity))) (le_of_eq h1)
  -- the real inequality `n^c * ((δ + 1/n) n)^L < n^L` after taking logarithms
  have hlog : (c : ℝ) * Real.log n + L * Real.log (δ + 1 / (n : ℝ)) < 0 := by
    have hinv : Real.log (1 / (δ + 1 / (n : ℝ))) = -Real.log (δ + 1 / (n : ℝ)) := by
      rw [one_div, Real.log_inv]
    rw [hinv] at hcond
    linarith
  have hkey : (n : ℝ) ^ c * (δ + 1 / (n : ℝ)) ^ L < 1 := by
    have hpos : (0 : ℝ) < (n : ℝ) ^ c * (δ + 1 / (n : ℝ)) ^ L := by positivity
    have hlt : Real.log ((n : ℝ) ^ c * (δ + 1 / (n : ℝ)) ^ L) < Real.log 1 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_one]
      exact hlog
    exact (Real.log_lt_log_iff hpos (by norm_num)).1 (by simpa using hlt)
  have hfinal : ((n : ℝ)) ^ c * (⌈δ * (n : ℝ)⌉₊ : ℝ) ^ L < (n : ℝ) ^ L := by
    have h1 : (⌈δ * (n : ℝ)⌉₊ : ℝ) ^ L ≤ ((δ + 1 / (n : ℝ)) * n) ^ L :=
      pow_le_pow_left₀ (by positivity) hm L
    calc ((n : ℝ)) ^ c * (⌈δ * (n : ℝ)⌉₊ : ℝ) ^ L
        ≤ (n : ℝ) ^ c * ((δ + 1 / (n : ℝ)) * n) ^ L := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((n : ℝ) ^ c * (δ + 1 / (n : ℝ)) ^ L) * (n : ℝ) ^ L := by rw [mul_pow]; ring
      _ < 1 * (n : ℝ) ^ L := by
          exact mul_lt_mul_of_pos_right hkey (by positivity)
      _ = (n : ℝ) ^ L := one_mul _
  exact_mod_cast hfinal
