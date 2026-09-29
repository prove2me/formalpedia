-- Prove2me | Theorems.Thm_MachineLearning_WignerSemicircle_scDensity_second_moment
-- name    : MachineLearning.WignerSemicircle.scDensity_second_moment
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:43:17.420625+00:00
-- url     : https://prove2.me/theorems/2e8c9e61-5794-4c9d-b587-d00b4f6daa2c
-- title:
--   The second moment (variance) of the radius-`1` semicircle distribution is
-- statement:
--   The second moment (variance) of the radius-`1` semicircle distribution is
--   `1/4`.  Equivalently `∫_{-1}^{1} x²·√(1-x²) dx = π/8`.
--
--   ```lean
--   theorem MachineLearning.WignerSemicircle.scDensity_second_moment: ∫ x in (-1 : ℝ)..1, x ^ 2 * scDensity x = 1 / 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/WignerSemicircle/Density.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/WignerSemicircle/Density.lean#L74

-- Thm stub generated from MachineLearning/WignerSemicircle/Density.lean
import Mathlib
import Definitions.Def_MachineLearning_WignerSemicircle_Density
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Wigner Semicircle Density

This file develops the analytic side of the Wigner semicircle law: the density
of the (radius-1) semicircle distribution,

  f(x) = (2/π) · √(1 - x²),

supported on `[-1, 1]`.  This is the probability density towards which the
empirical spectral measures of normalized Wigner ensembles converge.  We prove it
is a genuine probability density (nonnegative, symmetric, integrates to `1`) and
compute its low-order moments (mean `0`, second moment `1/4`).

## Main results

- `scDensity_nonneg`        — the density is nonnegative.
- `scDensity_symm`          — the density is even (symmetry of the spectrum).
- `scDensity_eq_zero`       — the density vanishes outside `[-1, 1]` (compact support).
- `scDensity_normalization` — `∫_{-1}^{1} f = 1` (total probability mass).
- `scDensity_mean_zero`     — `∫_{-1}^{1} x · f(x) dx = 0` (mean of the law).
- `scDensity_second_moment` — `∫_{-1}^{1} x² · f(x) dx = 1/4` (variance of the law).
-/

open MachineLearning.WignerSemicircle

open scoped Real
open MeasureTheory intervalIntegral

theorem MachineLearning.WignerSemicircle.scDensity_second_moment: ∫ x in (-1 : ℝ)..1, x ^ 2 * scDensity x = 1 / 4 := by sorry
