-- Prove2me | Definitions.Def_NumberTheory_ProfileFormModelSelection
-- name    : NumberTheory_ProfileFormModelSelection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:26.22038+00:00
-- url     : https://prove2.me/theorems/6db8c83e-2507-4e69-bdf5-d35ab58881f3
-- title:
--   Aether Catalog definitions — NumberTheory_ProfileFormModelSelection
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ProfileFormModelSelection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ProfileFormModelSelection.lean by skeleton subtraction
import Mathlib
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

namespace ProfileForm

open Real Filter Topology

/-- Akaike weight of the best model in a four-model comparison whose three
rivals sit at `ΔAICc = d₁, d₂, d₃`. -/
noncomputable def akaikeWeight (d₁ d₂ d₃ : ℝ) : ℝ :=
  1 / (1 + Real.exp (-d₁ / 2) + Real.exp (-d₂ / 2) + Real.exp (-d₃ / 2))












end ProfileForm


