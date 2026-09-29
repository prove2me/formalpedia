-- Prove2me | solution 1 for Bishop.dipFn_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:34:14.675812+00:00
-- url     : https://prove2.me/submissions/5c496a8b-53c1-4bf0-bf9f-37f2595cfb58

-- Sol generated from Logic/ConstructiveAnalysis/RootLocation.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Definitions.Def_Logic_ConstructiveAnalysis_RootLocation
/-
# Locating roots: what the grid search really delivers

`Bishop.exists_grid_abs_le` produces a grid point at which `|f|` is small.  Turning a
*small value* into a *small distance to a root* is the delicate step of the
intermediate value theorem, and `Bishop.constructive_ivt` does it with a global slope
bound `c > 0`, at the price of the factor `1/c`.

This file isolates the two sides of that step.

* `Bishop.exists_grid_near_root` : **the bracketing form of the search**.  With no
  non-degeneracy hypothesis whatsoever — only a modulus of uniform continuity and the
  sign condition `f a ≤ 0 ≤ f b` — the *sign-change* grid search returns a grid point
  within one mesh `(b-a)/N` of a genuine root.  The location comes from the bracket
  `f (grid k) ≤ 0 < f (grid (k+1))`, not from the size of `|f|`.

* `Bishop.local_nonconstancy_insufficient` : **a bound on `|f|` alone is not enough**,
  even under Bishop's local non-constancy hypothesis with an explicit modulus `ν`.
  The `1`-Lipschitz function `Bishop.dipFn η x = min (x-1) (|x-3| + η)` has the unique
  root `1`, satisfies local non-constancy with the explicit modulus `ν h = h/8`, and
  yet `|dipFn η 3| = η` is as small as one likes while `3` is at distance `2` from the
  root.  So no theorem of the form "`|f x|` small ⟹ `x` near a root" can be derived
  from local non-constancy alone.
-/


open Bishop

open Set

/-! ## 1. The bracketing form of the grid search -/


/-! ## 2. Local non-constancy does not locate approximate roots

Bishop's exact intermediate value theorem replaces a slope bound by *local
non-constancy*.  The following explicit function shows that this hypothesis, even
with an explicit modulus `ν`, does not let one conclude that a point with small
`|f|` is close to a root. -/











open Bishop in
theorem solution(η x y : ℝ) : |dipFn η x - dipFn η y| ≤ |x - y| := by
  have h1 : |dipFn η x - dipFn η y|
      ≤ max |(x - 1) - (y - 1)| |(|x - 3| + η) - (|y - 3| + η)| :=
    abs_min_sub_min_le_max _ _ _ _
  have h2 : |(x - 1) - (y - 1)| = |x - y| := by ring_nf
  have h3 : (|x - 3| + η) - (|y - 3| + η) = |x - 3| - |y - 3| := by ring
  have h4 : |(|x - 3| + η) - (|y - 3| + η)| ≤ |x - y| := by
    rw [h3]
    have hbd := abs_abs_sub_abs_le_abs_sub (x - 3) (y - 3)
    have he : (x - 3) - (y - 3) = x - y := by ring
    rw [he] at hbd
    exact hbd
  rw [h2] at h1
  exact h1.trans (max_le le_rfl h4)
