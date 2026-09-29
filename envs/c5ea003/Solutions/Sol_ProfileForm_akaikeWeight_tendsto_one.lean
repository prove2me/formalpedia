-- Prove2me | solution 1 for ProfileForm.akaikeWeight_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:32.892959+00:00
-- url     : https://prove2.me/submissions/d7b16462-7a27-4d9e-855c-2d54c1d1eac7

-- Sol generated from NumberTheory/ProfileFormModelSelection.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormModelSelection
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

/-!
# Profile form III: the model-selection verdict is a theorem, not a judgement

Context (experiment 579, paper 229; V1 rule).  The power-law profile won the
pre-registered model comparison with reported Akaike weight `0.9866` against
three rivals at `ΔAICc = +9.2` (exponential), `+11.5` (logistic, degenerate)
and `+16.9` (linear).

The Akaike weight of the best model in a four-model set with gaps
`d₁, d₂, d₃ ≥ 0` is

`w(d₁,d₂,d₃) = 1 / (1 + exp(-d₁/2) + exp(-d₂/2) + exp(-d₃/2))`.

Everything about the verdict except the fitted numbers is deterministic, and
that part is proved here:

* `akaikeWeight_mem_Ioo` — the weight is a genuine probability;
* `akaikeWeight_monotone_left` (and the symmetric variants) — widening any gap
  can only strengthen the winner;
* `akaikeWeight_lt_of_zero_gap` — a tied rival caps the weight at `1/2`, so a
  large weight is *evidence*, not an artefact of the normalisation;
* `akaikeWeight_ge_of_gaps` — a uniform lower bound `1/(1+3e^{-d/2})` in terms
  of the smallest gap;
* `akaikeWeight_exp579_gt` — with the measured gaps the weight exceeds `0.98`,
  confirming the reported `0.9866` to the accuracy that rigorous exponential
  bounds allow;
* `akaikeWeight_tendsto_one` — the weight saturates at `1` as the gaps grow.

The numerical bounds rest only on `Real.exp_one_gt_d9` and `Real.add_one_le_exp`
(`exp_four_ge`, `exp_neg_le_inv`); the file shares the `ProfileForm` namespace
with `NumberTheory.ProfileFormPowerLaw`.
-/

open ProfileForm

open Real Filter Topology














open ProfileForm in
theorem solution:
    Tendsto (fun d : ℝ => akaikeWeight d d d) atTop (𝓝 1) := by
  have hexp : Tendsto (fun d : ℝ => Real.exp (-d / 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun d : ℝ => -d / 2) atTop atBot := by
      apply Filter.Tendsto.atBot_div_const (by norm_num)
      exact tendsto_neg_atTop_atBot
    exact Real.tendsto_exp_atBot.comp h
  have hden : Tendsto
      (fun d : ℝ => 1 + Real.exp (-d / 2) + Real.exp (-d / 2) + Real.exp (-d / 2))
      atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ)) (f := atTop)).add hexp).add hexp |>.add hexp
    simpa using this
  have := hden.inv₀ (by norm_num)
  simpa [akaikeWeight, one_div] using this
