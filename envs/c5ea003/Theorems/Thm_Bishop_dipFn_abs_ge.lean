-- Prove2me | Theorems.Thm_Bishop_dipFn_abs_ge
-- name    : Bishop.dipFn_abs_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:13.002831+00:00
-- url     : https://prove2.me/theorems/c924c889-9848-4beb-9451-74c79abe5f3a
-- title:
--   Away from the two critical points `1` and `3`, the value of `dipFn η` is large.
-- statement:
--   Away from the two critical points `1` and `3`, the value of `dipFn η` is large.
--
--   ```lean
--   theorem Bishop.dipFn_abs_ge{η h z : ℝ} (hη : 0 < η) (h1 : h / 8 ≤ |z - 1|)
--       (h3 : h / 8 ≤ |z - 3|) : h / 8 ≤ |dipFn η z| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/RootLocation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/RootLocation.lean#L133

-- Thm stub generated from Logic/ConstructiveAnalysis/RootLocation.lean
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

theorem Bishop.dipFn_abs_ge{η h z : ℝ} (hη : 0 < η) (h1 : h / 8 ≤ |z - 1|)
    (h3 : h / 8 ≤ |z - 3|) : h / 8 ≤ |dipFn η z| := by sorry
