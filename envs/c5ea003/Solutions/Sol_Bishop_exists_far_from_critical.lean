-- Prove2me | solution 1 for Bishop.exists_far_from_critical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:37:55.129382+00:00
-- url     : https://prove2.me/submissions/3db8eb9e-3431-4103-8655-2e65ec7371ef

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
theorem solution{x y h : ℝ} (hh : 0 < h) (hxy : x + h ≤ y) :
    ∃ z ∈ Icc x y, h / 8 ≤ |z - 1| ∧ h / 8 ≤ |z - 3| := by
  by_contra hcon
  push_neg at hcon
  have hp0 : |x - 1| < h / 8 ∨ |x - 3| < h / 8 := by
    by_cases hb : h / 8 ≤ |x - 1|
    · exact Or.inr (hcon x ⟨le_rfl, by linarith⟩ hb)
    · exact Or.inl (not_le.mp hb)
  have hp1 : |x + h / 3 - 1| < h / 8 ∨ |x + h / 3 - 3| < h / 8 := by
    have hmem : x + h / 3 ∈ Icc x y := ⟨by linarith, by linarith⟩
    by_cases hb : h / 8 ≤ |x + h / 3 - 1|
    · exact Or.inr (hcon _ hmem hb)
    · exact Or.inl (not_le.mp hb)
  have hp2 : |x + 2 * h / 3 - 1| < h / 8 ∨ |x + 2 * h / 3 - 3| < h / 8 := by
    have hmem : x + 2 * h / 3 ∈ Icc x y := ⟨by linarith, by linarith⟩
    by_cases hb : h / 8 ≤ |x + 2 * h / 3 - 1|
    · exact Or.inr (hcon _ hmem hb)
    · exact Or.inl (not_le.mp hb)
  rcases hp0 with h0 | h0 <;> rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2 <;>
    · rw [abs_lt] at h0 h1 h2
      linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
