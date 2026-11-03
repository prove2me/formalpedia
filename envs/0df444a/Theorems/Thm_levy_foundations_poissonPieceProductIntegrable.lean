-- Prove2me | Theorems.Thm_levy_foundations_poissonPieceProductIntegrable
-- name    : levy_foundations_poissonPieceProductIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:36:15.047985+00:00
-- url     : https://prove2.me/theorems/8561bce0-c61b-442a-b787-089c888162bd
-- title:
--   Integrability of bounded products over a random Poisson number of marks
-- statement:
--   A product of norm-at-most-one measurable complex mark weights over any finite random Poisson count is strongly measurable and uniformly norm-bounded by one, hence integrable on a probability space.
-- source:
--   Inspired by LeanLevy PoissonPointFamily.lean lines 1022–1035, MIT licence, commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored draft, uncompiled.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory

theorem levy_foundations_poissonPieceProductIntegrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) (w : E → ℂ)
    (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    Integrable (fun ω =>
      ∏ n ∈ Finset.range (K k ω), w (X k n ω)) μ := by sorry
