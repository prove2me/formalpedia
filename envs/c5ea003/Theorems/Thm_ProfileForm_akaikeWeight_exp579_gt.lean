-- Prove2me | Theorems.Thm_ProfileForm_akaikeWeight_exp579_gt
-- name    : ProfileForm.akaikeWeight_exp579_gt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:34:53.590734+00:00
-- url     : https://prove2.me/theorems/55b26b8b-f9d3-490f-b4d2-33865d55eafe
-- title:
--   The measured verdict.
-- statement:
--   **The measured verdict.**  With `ΔAICc = 9.2, 11.5, 16.9` the Akaike weight
--   of the power law exceeds `0.98`.
--
--   ```lean
--   theorem ProfileForm.akaikeWeight_exp579_gt: 0.98 < akaikeWeight 9.2 11.5 16.9 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormModelSelection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormModelSelection.lean#L130

-- Thm stub generated from NumberTheory/ProfileFormModelSelection.lean
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

theorem ProfileForm.akaikeWeight_exp579_gt: 0.98 < akaikeWeight 9.2 11.5 16.9 := by sorry
