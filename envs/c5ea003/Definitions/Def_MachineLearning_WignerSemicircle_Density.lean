-- Prove2me | Definitions.Def_MachineLearning_WignerSemicircle_Density
-- name    : MachineLearning_WignerSemicircle_Density
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:20:33.107197+00:00
-- url     : https://prove2.me/theorems/02420680-927d-40b4-942c-929618d35de5
-- title:
--   Aether Catalog definitions — MachineLearning_WignerSemicircle_Density
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.WignerSemicircle.Density`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/WignerSemicircle/Density.lean by skeleton subtraction
import Mathlib
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

namespace MachineLearning.WignerSemicircle

open scoped Real
open MeasureTheory intervalIntegral

/-- The density of the radius-`1` Wigner semicircle distribution,
`f(x) = (2/π)·√(1 - x²)`.  Outside `[-1,1]` the argument of the square root is
negative, so `Real.sqrt` returns `0` and the density has compact support. -/
noncomputable def scDensity (x : ℝ) : ℝ := (2 / Real.pi) * Real.sqrt (1 - x ^ 2)







end MachineLearning.WignerSemicircle


