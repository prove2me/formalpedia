-- Prove2me | Theorems.Thm_mderiv_closable
-- name    : mderiv_closable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:23.945329+00:00
-- url     : https://prove2.me/theorems/5bfae219-59ae-5bf7-a182-451c88a84571
-- title:
--   mderiv closable: mderiv closable
-- statement:
--   The mderiv closable construction uses the mderiv closable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Solution.lean#L200-L213
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Solution.lean#L200-L213

import Definitions.Def_Malliavin
import Definitions.Def_Malliavin_Solution
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace

theorem mderiv_closable
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ]
    (F : ℕ → {F : W → ℝ // IsSmoothBounded F})
    {η : Lp (CameronMartin.Space μ) 2 μ}
    (hF : Tendsto (fun k ↦ (F k).2.toLp μ) atTop (𝓝 0))
    (hD : Tendsto (fun k ↦ (F k).2.mderivLp μ) atTop (𝓝 η)) :
    η = 0 := by sorry
