-- Prove2me | solution 1 for DenseSumsetLower.cube_dimension_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:49.842756+00:00
-- url     : https://prove2.me/submissions/69ae3d06-1e71-4de8-8e32-b8c17840d32b

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
theorem solution{δ ε : ℝ} (h0 : 0 < δ) (h1 : δ < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ d : ℕ,
      (1 + ε) * (((d : ℝ) + 1) * Real.log n) ≤ (2 ^ d : ℕ) * Real.log (1 / δ) →
      ¬ ((4 / δ) ^ (2 ^ d) ≤ 2 * (n : ℝ)) := by
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, Real.log 2 / ε < Real.log n := by
    have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hlog.eventually_gt_atTop _
  filter_upwards [Filter.eventually_ge_atTop 2, hlarge] with n hn2 hnbig
  intro d hd hex
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hlpos : 0 < Real.log (1 / δ) := by
    simp only [one_div]
    exact Real.log_pos (by rw [lt_inv_comm₀ (by norm_num) h0]; simpa using h1)
  -- the existence condition gives `2^d log(4/δ) ≤ log 2 + log n`, hence
  -- `2^d log(1/δ) ≤ log 2 + log n`, since `log (4/δ) ≥ log (1/δ)`
  have hlog4 : Real.log (1 / δ) ≤ Real.log (4 / δ) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right h0]
    norm_num
  have hkey : ((2 ^ d : ℕ) : ℝ) * Real.log (4 / δ) ≤ Real.log 2 + Real.log n := by
    have h2 : Real.log ((4 / δ) ^ (2 ^ d)) ≤ Real.log (2 * n) :=
      Real.log_le_log (by positivity) hex
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h2
    exact_mod_cast h2
  have hpow1 : (1 : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  have hbound : ((2 ^ d : ℕ) : ℝ) * Real.log (1 / δ) ≤ Real.log 2 + Real.log n := by
    refine le_trans (mul_le_mul_of_nonneg_left hlog4 (by positivity)) hkey
  -- but the avoidance condition forces `2^d log(1/δ) ≥ (1+ε) log n > log 2 + log n`
  -- once `n` is large; we only need `d ≥ 0`, `log 2 ≤ log n` fails for small `n`, so we
  -- argue with the parameter factor `(d+1) ≥ 1` instead.
  have hlow : (1 + ε) * Real.log n ≤ ((2 ^ d : ℕ) : ℝ) * Real.log (1 / δ) := by
    refine le_trans ?_ hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hstep : Real.log n ≤ ((d : ℝ) + 1) * Real.log n :=
      le_mul_of_one_le_left hlogn.le hd1
    exact mul_le_mul_of_nonneg_left hstep (by linarith)
  -- combining: `(1+ε) log n ≤ log 2 + log n`, i.e. `ε log n ≤ log 2`
  have hcomb : ε * Real.log n ≤ Real.log 2 := by linarith
  rw [div_lt_iff₀ hε] at hnbig
  nlinarith
