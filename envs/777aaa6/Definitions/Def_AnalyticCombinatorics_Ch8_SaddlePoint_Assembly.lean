-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:09:21.268605+00:00
-- url     : https://prove2.me/theorems/22f2bfd3-a03a-4784-8acf-a354f001d95d
-- title:
--   Circle-integral saddle extraction
-- statement:
--   For a complex function, radius and coefficient index, define the raw oscillatory integrand, its normalized ratio by f(r), the prefactor f(r)/r^n, and full/central/tail angular integrals with factor1/(2pi). Sequence versions evaluate these at r_n and window delta_n. The final scale divides the prefactor by sqrt(2pi B_n).
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Assembly.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Saddle-point assembly bricks

This file contains the exact Cauchy parameterization on `[-pi, pi]` and the
bounded algebraic assembly theorem for a central/tail saddle decomposition.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal

noncomputable section

/-- The unnormalized Cauchy integrand after the circle parameterization. -/
def saddleRawIntegrand (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  f ((r : ℂ) * Complex.exp (θ * Complex.I)) * Complex.exp (-(↑↑n * ↑θ) * Complex.I)

/-- The normalized saddle integrand at a fixed radius. -/
def saddleGAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ) *
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)

/-- The saddle prefactor at a fixed radius. -/
def saddlePrefAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  f (r : ℂ) / (r : ℂ) ^ n

/-- The full normalized integral at a fixed radius. -/
def saddleJfullAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ

/-- The central normalized integral at a fixed radius and window. -/
def saddleJcAt (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-δ)..δ, saddleGAt f r n θ

/-- The two tail arcs at a fixed radius and window. -/
def saddleJtAt (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
      ∫ θ in δ..Real.pi, saddleGAt f r n θ)

/-- Sequence version of the normalized saddle integrand. -/
def saddleG (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  saddleGAt f (r n) n θ

/-- Sequence version of the saddle prefactor. -/
def saddlePref (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddlePrefAt f (r n) n

/-- Sequence version of the full normalized integral. -/
def saddleJfull (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJfullAt f (r n) n

/-- Sequence version of the central normalized integral. -/
def saddleJc (f : ℂ → ℂ) (r δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJcAt f (r n) (δ n) n

/-- Sequence version of the normalized tail arcs. -/
def saddleJt (f : ℂ → ℂ) (r δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJtAt f (r n) (δ n) n

/-- The final saddle scale `f(r_n)/(r_n^n sqrt(2*pi*B_n))`. -/
def saddleScale (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddlePref f r n / (Real.sqrt (2 * Real.pi * B n) : ℂ)


