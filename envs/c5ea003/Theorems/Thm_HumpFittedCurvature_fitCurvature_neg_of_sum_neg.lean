-- Prove2me | Theorems.Thm_HumpFittedCurvature_fitCurvature_neg_of_sum_neg
-- name    : HumpFittedCurvature.fitCurvature_neg_of_sum_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:38:16.620655+00:00
-- url     : https://prove2.me/theorems/d287bbab-55e2-456c-b2a5-a575350a1b62
-- title:
--   Passing from the numerator to the normalised statistic.
-- statement:
--   Passing from the numerator to the normalised statistic.
--
--   ```lean
--   theorem HumpFittedCurvature.fitCurvature_neg_of_sum_neg(n : ℕ) (t : ℕ → ℝ) (q g : ℝ → ℝ)
--       (hnum : ∑ i ∈ range n, g (t i) * q (t i) < 0) : fitCurvature n t q g < 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/HumpFittedCurvature.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/HumpFittedCurvature.lean#L428

-- Thm stub generated from Algebra/HumpFittedCurvature.lean
import Mathlib
import Definitions.Def_Algebra_HumpFittedCurvature
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

open HumpFittedCurvature

open Finset Set HumpWindowGeometry

/-! ## 1. The fitted curvature statistic -/


/-! ## 2. Concave profiles versus the chord through the roots -/

variable {S : Set ℝ} {g : ℝ → ℝ} {r₁ r₂ : ℝ}








/-! ## 3. The sign theorem -/








/-! ## 4. The equal-width bin grid of the pipeline -/















/-! ## 5. Bin-width and grid-shift invariance of the measured curvature -/

theorem HumpFittedCurvature.fitCurvature_neg_of_sum_neg(n : ℕ) (t : ℕ → ℝ) (q g : ℝ → ℝ)
    (hnum : ∑ i ∈ range n, g (t i) * q (t i) < 0) : fitCurvature n t q g < 0 := by sorry
