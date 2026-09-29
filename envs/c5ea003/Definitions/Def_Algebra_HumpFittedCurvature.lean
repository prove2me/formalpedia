-- Prove2me | Definitions.Def_Algebra_HumpFittedCurvature
-- name    : Algebra_HumpFittedCurvature
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:23:44.899103+00:00
-- url     : https://prove2.me/theorems/913e7172-a87d-473a-86cc-df6622727daf
-- title:
--   Aether Catalog definitions — Algebra_HumpFittedCurvature
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.HumpFittedCurvature`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/HumpFittedCurvature.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_HumpWindowGeometry
/-
# The fitted quadratic coefficient is a certificate of concavity

Second formal core of experiment **581** (paper 231).  The experiment's central
descriptive statistic is the **quadratic-fit curvature** `c` of the binned ratio
profile `R = T/M`: `c = -0.105` pooled controls, `c = -0.299` dominant band,
`c = -0.18 / -0.25 / -0.44` in the three LPF terciles, `c = -0.13` in the first
`k100` tercile.  The verdict language ("concave in ALL THREE") reads a negative
fitted `c` as *concavity of the underlying profile*.

That reading is not automatic: `c` is an inner product of the profile against a
grid-dependent orthogonal quadratic, and one has to know that this inner product
cannot be negative for an accident of the grid.  This file proves it, in the
exact discrete form used by the pipeline (finitely many equal-width bins).

## Main results

* `HumpFittedCurvature.sum_profile_mul_quadratic_nonpos` — **sign theorem**: for
  any concave profile `g`, any finite grid, and any quadratic
  `q(y) = (y-r₁)(y-r₂)` that is orthogonal to constants and to the identity on
  that grid, `∑ g(tᵢ) q(tᵢ) ≤ 0`.  The proof subtracts the chord of `g` through
  the two roots of `q`; orthogonality kills the chord, and the residual has the
  opposite sign to `q` at every single grid point.
* `HumpFittedCurvature.sum_profile_mul_quadratic_neg` — strict version for
  strictly concave profiles.
* `HumpFittedCurvature.affine_profile_sum_eq_zero` — the **control**:
  an affine profile fits with curvature exactly `0`, matching the experiment's
  "controls clean everywhere".
* `HumpFittedCurvature.binGrid_orth_const`, `binGrid_orth_id` — the equal-width
  bin grid of the pipeline, with the explicit orthogonal quadratic
  `q(y) = (y-m)² - h²·V(n)`, is orthogonal to constants and to the identity for
  **every** bin width `h` and **every** grid centre `m`.
* `HumpFittedCurvature.fitCurvature_neg_binGrid` — hence for any strictly
  concave profile the measured curvature is strictly negative.
* `HumpFittedCurvature.window_fitCurvature_neg` — applied to the `j² − N`
  log-size profile of `Algebra.HumpWindowGeometry`: **the geometric channel `H0`
  predicts a strictly negative fitted curvature, for every bin width and every
  grid offset.**  This is exactly the pre-registered "bin-width permutation /
  u-grid shift" probe, and `H0` passes it: the concavity sign is invariant.

Together with `HumpWindowGeometry.vertex_lt_midpoint` this sharpens the verdict:
the geometry predicts the *sign* robustly but cannot place the *vertex*.
-/

namespace HumpFittedCurvature

open Finset Set HumpWindowGeometry

/-! ## 1. The fitted curvature statistic -/

/-- The least-squares quadratic coefficient of a profile `g` sampled at the grid
points `t 0, …, t (n-1)`, read against a quadratic `q` orthogonal to constants
and to the identity on the grid. -/
noncomputable def fitCurvature (n : ℕ) (t : ℕ → ℝ) (q g : ℝ → ℝ) : ℝ :=
  (∑ i ∈ range n, g (t i) * q (t i)) / (∑ i ∈ range n, q (t i) ^ 2)

/-! ## 2. Concave profiles versus the chord through the roots -/

variable {S : Set ℝ} {g : ℝ → ℝ} {r₁ r₂ : ℝ}








/-! ## 3. The sign theorem -/








/-! ## 4. The equal-width bin grid of the pipeline -/

/-- Centred index offset of bin `i` out of `n`. -/
noncomputable def off (n : ℕ) (i : ℕ) : ℝ := (i : ℝ) - ((n : ℝ) - 1) / 2

/-- Bin centres: `n` equal bins of width `h`, grid centre `m`. -/
noncomputable def binGrid (n : ℕ) (m h : ℝ) (i : ℕ) : ℝ := m + h * off n i

/-- Mean square offset of the bin grid. -/
noncomputable def gridVar (n : ℕ) : ℝ := (∑ i ∈ range n, (off n i) ^ 2) / n






/-- Half-width of the orthogonal quadratic's root pair. -/
noncomputable def rootHalf (n : ℕ) (h : ℝ) : ℝ := h * Real.sqrt (gridVar n)






/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/





end HumpFittedCurvature


