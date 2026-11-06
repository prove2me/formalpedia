-- Prove2me | Theorems.Thm_levy_foundations_existsSmallJumpMartingaleVersion
-- name    : levy_foundations_existsSmallJumpMartingaleVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:11:33.624457+00:00
-- url     : https://prove2.me/theorems/b17e8924-2ad0-41b8-963f-dde86b1e54f2
-- title:
--   Adapted martingale version of the compensated small-jump integral
-- statement:
--   Construct an adapted, integrable martingale whose time slices represent the compensated small-jump L² integral almost everywhere; establish its natural-filtration martingale property.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), PoissonMartingale.lean lines 517–549, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Private draft awaiting remote Lean verification.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_levy_foundations_prmFiltration
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
open scoped NNReal

open MeasureTheory ProbabilityTheory

theorem levy_foundations_existsSmallJumpMartingaleVersion
    {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure ℝ) [SigmaFinite ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod ν) μ)
    (hν : LevyFoundations.isLevyMeasure ν)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t : ℝ≥0,
        Y t =ᵐ[μ] (fun ω =>
          LevyFoundations.smallJumpIntegralLp ν μ I hν (t : ℝ) ω)) ∧
      MeasureTheory.Martingale Y
        (LevyFoundations.prmFiltration K X ν
          hd.measurable_count hd.measurable_point) μ := by sorry
