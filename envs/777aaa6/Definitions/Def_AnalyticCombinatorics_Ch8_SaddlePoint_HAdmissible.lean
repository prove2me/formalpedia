-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:12:17.014901+00:00
-- url     : https://prove2.me/theorems/43756089-94d5-4159-ab65-c1dc8e78a117
-- title:
--   Admissibility records and saddle sequences
-- statement:
--   The local ratio divides f(re^(i theta))/f(r) times its centered phase by the Gaussian term. HAdmissible stores the actual Taylor expansion, positive radius, nontrivial radial filter, real a,b,delta and proved eventual positivity, disk differentiability, local Gaussian and uniform tail properties. SaddleSequence stores radii tending to that filter and an eventual a(r_n)=n identity. Derived B/Delta functions evaluate b/delta along the sequence, and centralD is a Gaussian dominator.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/HAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
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
# H-admissible saddle-point bridge

This file packages the abstract H-admissible hypotheses needed to feed the
central Gaussian core, the tail estimate, and the Cauchy assembly theorem.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Relative local error after removing the saddle phase and Gaussian. -/
def saddleLocalRatio (f : ℂ → ℂ) (a b : ℝ → ℝ) (r θ : ℝ) : ℂ :=
  (f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ) *
      Complex.exp (-(a r * θ : ℝ) * Complex.I)) /
    Complex.exp (-(b r * θ ^ 2 / 2 : ℝ))

/-- Abstract H-admissible saddle data for an analytic function. -/
structure HAdmissible (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) where
  ρ : ℝ≥0∞
  radFilter : Filter ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  δ : ℝ → ℝ

  hp : HasFPowerSeriesAt f p 0
  radius_eq : p.radius = ρ
  radius_pos : 0 < ρ
  rad_neBot : radFilter.NeBot

  r_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < r
  differentiableOn :
    ∀ᶠ (r : ℝ) in radFilter, DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)
  f_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < (f (r : ℂ)).re
  b_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < b r
  δ_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < δ r
  δ_le_pi : ∀ᶠ (r : ℝ) in radFilter, δ r ≤ Real.pi

  δ_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => δ r * Real.sqrt (b r)) radFilter atTop

  local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in radFilter, ∀ θ : ℝ, |θ| ≤ δ r →
      ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε

  tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in radFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * b r) * E r)
        radFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        δ r ≤ |θ| → |θ| ≤ Real.pi → ‖saddleGAt f r n θ‖ ≤ E r)

/-- A sequence of saddle radii tracking the admissible radius filter. -/
structure SaddleSequence {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) where
  r : ℕ → ℝ
  tendsTo : Tendsto r atTop hf.radFilter
  saddle_eq : ∀ᶠ n in atTop, hf.a (r n) = (n : ℝ)

namespace HAdmissible

/-- Sequence version of the admissible quadratic scale. -/
abbrev B {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.b (hr.r n)

/-- Sequence version of the admissible central window. -/
abbrev Δ {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.δ (hr.r n)

@[simp] theorem B_apply {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) (n : ℕ) :
    B hf hr n = hf.b (hr.r n) := rfl

@[simp] theorem Δ_apply {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) (n : ℕ) :
    Δ hf hr n = hf.δ (hr.r n) := rfl

end HAdmissible

def centralD (x : ℝ) : ℝ := 2 * Real.exp (-(x ^ 2) / 2)


