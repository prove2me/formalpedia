-- Prove2me | Theorems.Thm_levy_foundations_poissonPGFSeries
-- name    : levy_foundations_poissonPGFSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:32:36.905588+00:00
-- url     : https://prove2.me/theorems/fbfc49fd-4806-4357-b60f-9be0b69af755
-- title:
--   Complex Poisson generating series sums to an exponential
-- statement:
--   The complex probability generating series of a Poisson distribution with rate lam equals exp(lam(w−1)) for every complex w, including the zero-rate case.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Target requires remote Lean elaboration.  Source lines 890–901.

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

theorem levy_foundations_poissonPGFSeries
    (lam : ℝ≥0) (w : ℂ) :
    ∑' j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j =
      Complex.exp ((lam : ℝ) * (w - 1)) := by sorry
