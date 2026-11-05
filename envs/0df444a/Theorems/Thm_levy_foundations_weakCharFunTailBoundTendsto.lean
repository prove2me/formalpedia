-- Prove2me | Theorems.Thm_levy_foundations_weakCharFunTailBoundTendsto
-- name    : levy_foundations_weakCharFunTailBoundTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:19:43.785008+00:00
-- url     : https://prove2.me/theorems/f56de1af-a8f9-4193-b6c0-5954214c63ae
-- title:
--   Continuous characteristic function has vanishing Fourier tail bound
-- statement:
--   Continuous characteristic function has vanishing Fourier tail bound.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean#L195

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_levy_foundations_probabilityCharacteristicFun
import Definitions.Def_levy_foundations_weakCharFunTendsto
import Definitions.Def_levy_foundations_weakExpBCF

open MeasureTheory Complex ComplexConjugate Filter Topology BoundedContinuousFunction

theorem levy_foundations_weakCharFunTailBoundTendsto
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : φ 0 = 1) :
    Tendsto (fun r => 2⁻¹ * r *
      ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖)
      atTop (𝓝 0) := by sorry
