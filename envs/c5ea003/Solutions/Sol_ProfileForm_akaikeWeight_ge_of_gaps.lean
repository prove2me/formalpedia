-- Prove2me | solution 1 for ProfileForm.akaikeWeight_ge_of_gaps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:32.317524+00:00
-- url     : https://prove2.me/submissions/c5bf7596-dc77-40fd-b80f-d521b0b0b414

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


theorem akaikeWeight_denom_pos (d₁ d₂ d₃ : ℝ) :
    0 < 1 + Real.exp (-d₁ / 2) + Real.exp (-d₂ / 2) + Real.exp (-d₃ / 2) := by
  have h1 := Real.exp_pos (-d₁ / 2)
  have h2 := Real.exp_pos (-d₂ / 2)
  have h3 := Real.exp_pos (-d₃ / 2)
  linarith












open ProfileForm in
theorem solution{d d₁ d₂ d₃ : ℝ} (h1 : d ≤ d₁) (h2 : d ≤ d₂)
    (h3 : d ≤ d₃) :
    1 / (1 + 3 * Real.exp (-d / 2)) ≤ akaikeWeight d₁ d₂ d₃ := by
  have e1 : Real.exp (-d₁ / 2) ≤ Real.exp (-d / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have e2 : Real.exp (-d₂ / 2) ≤ Real.exp (-d / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have e3 : Real.exp (-d₃ / 2) ≤ Real.exp (-d / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have hd := akaikeWeight_denom_pos d₁ d₂ d₃
  have hpos : (0:ℝ) < 1 + 3 * Real.exp (-d / 2) := by
    have := Real.exp_pos (-d / 2); linarith
  rw [akaikeWeight, div_le_div_iff₀ hpos hd]
  linarith
