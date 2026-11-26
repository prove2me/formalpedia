-- Prove2me | Theorems.Thm_integral_inner_mderiv
-- name    : integral_inner_mderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:41.012284+00:00
-- url     : https://prove2.me/theorems/dd33233e-605d-4c47-9654-2410c8afa3fd
-- title:
--   integral inner mderiv: integral inner mderiv
-- statement:
--   Gaussian integration by parts: the mean directional Malliavin derivative
--   along a Cameron–Martin vector equals pairing against its first-chaos
--   representative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Solution.lean#L187-L198
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Solution.lean#L187-L198

import Definitions.Def_Malliavin
import Definitions.Def_Malliavin_Solution
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace

theorem integral_inner_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ]
    {F : W → ℝ} (hF : IsSmoothBounded F) (h : CameronMartin.Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ =
      ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ := by sorry
