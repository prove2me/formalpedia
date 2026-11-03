-- Prove2me | Theorems.Thm_levy_foundations_compensatedPoissonL2ExtensionUnique
-- name    : levy_foundations_compensatedPoissonL2ExtensionUnique
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:20:34.80957+00:00
-- url     : https://prove2.me/theorems/40b91799-45bb-4d62-ba5a-ef118270cd1e
-- title:
--   Uniqueness of the L² compensated integral extension
-- statement:
--   Two linear L² isometries that agree almost everywhere with the same compensated point-series on the dense L¹∩L² class agree on all of L².
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonCompensated.lean; independently authored Prove2Me draft pending remote elaboration. Uniqueness follows from L¹∩L² density and continuity of linear isometries, supporting the extension near lines 699–761.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension

open MeasureTheory

theorem levy_foundations_compensatedPoissonL2ExtensionUnique
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (I J : Lp ℝ 2 m → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension m μ K X I)
    (hJ : LevyFoundations.IsCompensatedPoissonL2Extension m μ K X J) :
    I = J := by sorry
