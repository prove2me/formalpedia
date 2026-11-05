-- Prove2me | Theorems.Thm_levy_foundations_prmFiltrationApply
-- name    : levy_foundations_prmFiltrationApply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:55:30.354045+00:00
-- url     : https://prove2.me/theorems/ede0da15-3b8e-49f0-9ab0-8b35afcaee7c
-- title:
--   Natural Poisson filtration evaluated at time t
-- statement:
--   At nonnegative time t, the natural filtration is exactly the sigma-algebra of Poisson random-measure evaluations on the time-prefix (-∞,t] × E.
-- source:
--   Inspired by Shmuel Link's MIT-licensed LeanLevy/RandomMeasure/PoissonMartingale.lean, theorem prmFiltration_apply (lines 97–100), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_levy_foundations_prmFiltration

open MeasureTheory
open scoped NNReal

theorem levy_foundations_prmFiltrationApply
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (m : Measure E) [SigmaFinite m]
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n))
    (t : ℝ≥0) :
    LevyFoundations.prmFiltration K X m hK hX t =
      LevyFoundations.prmEvalSigma K X (volume.prod m)
        (Set.Iic (t : ℝ) ×ˢ Set.univ) := by sorry
