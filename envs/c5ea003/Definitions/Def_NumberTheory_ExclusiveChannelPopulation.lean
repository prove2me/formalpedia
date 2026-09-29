-- Prove2me | Definitions.Def_NumberTheory_ExclusiveChannelPopulation
-- name    : NumberTheory_ExclusiveChannelPopulation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:54.409888+00:00
-- url     : https://prove2.me/theorems/69c9ce89-67ad-4a14-8f17-1c552bc90b0a
-- title:
--   Aether Catalog definitions — NumberTheory_ExclusiveChannelPopulation
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ExclusiveChannelPopulation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ExclusiveChannelPopulation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
/-
# NET-30 / Catalog·NumberTheory — A saturating-gate population model: the k = 2
signature realised, and the k = 1 arms shown to be unconstrained

The two companion files are *negative*: the measured s = 13, k = 2 signature
(single-coordinate ablations inside the no-op band, whole-block ablation costing
0.24, sign flip costing as much) is impossible for an affine read-out
(`NumberTheory.ExclusiveChannelInterventions`) and, more sharply, for any convex
one (`NumberTheory.ExclusiveChannelConvexity`).  This file supplies the matching
*positive* half: an explicit, fully computed model in which the entire published
NET-30 s = 13 row is reproduced, and a theorem showing the Part B (`k = 1`) rows
carry no information at all about the model class.

Ingredients.

* `ItemPopulation`: a finite population of evaluation items with masses summing
  to `1`, item `i` being answered correctly exactly when the boundary gate value
  reaches its difficulty threshold `thr i`.  `ItemPopulation.acc γ` is the
  accuracy at gate value `γ`; it is monotone in `γ` (`acc_mono`).
* `satGate`: the saturating boundary gate `min (max (∑ i, c i) 0) 1` on the
  exclusive coefficients — rectified (hence sign-sensitive) and saturating
  (hence redundant).
* `s13_k2_saturating_realization`: one population, one coefficient vector
  `c = ![1, 1]`, and **all six** published s = 13 arm numbers reproduced to
  within `0.005` (the reported no-op scale): `ctl 0.9980`, `zeroAt 0 0.9961`,
  `zeroAt 1 0.9990`, `zeroAll 0.7544`, `flipAt 0 0.7505`, `scale 0.1 0.9067`.
  The model *predicts* the exact no-op of both single ablations and the
  simultaneous sign- and magnitude-sensitivity, which is what the arm shows.
* `acc_scaleAll_mono`: the scale curve is monotone, so `zeroAll ≤ scale l ≤ ctl`
  — matching the measured `0.7544 ≤ 0.9067 ≤ 0.9980` ordering.
* `missing_middle_sharp`: the headline. In this model class the
  "1-redundant but block-dependent" phenomenon **occurs at k = 2** and
  **cannot occur at k ≤ 1** — the formal statement of "the missing middle".
* `interventions_noop_of_boundary_free`, `noop_all_iff_acc_zero_eq`: a
  boundary-free arm (control accuracy already equal to the zero-gate accuracy)
  is unchanged by every gate-weakening intervention, and that is the *only* way
  for all of them to be no-ops.  This is the pooled Part B invariant — the
  failed arms are no-ops in every arm of both rounds — and it shows such a
  no-op is evidence that the channel was never used, not of internalisation.
* `k1_profile_unconstrained`: at `k = 1` *every* admissible pair of control and
  ablation accuracies `0 ≤ β ≤ α ≤ 1` is realised by some population.  The
  seed-heterogeneous Part B outcomes (two exact self-sufficient cures, two
  no-ops, two ~2 SE marginal losses) are therefore all inside the same class:
  no `k = 1` observation constrains it, which is precisely why the
  proportionality law it was used to support does not survive.
-/


namespace NumberTheory.ExclusiveChannel

open Finset

/-! ## Populations of evaluation items -/

/-- A finite population of evaluation items: item `i` carries mass `mass i`
(the masses sum to one) and is answered correctly exactly when the boundary gate
value reaches the difficulty threshold `thr i`. -/
structure ItemPopulation where
  /-- number of item groups -/
  n : ℕ
  /-- mass (relative frequency) of each group -/
  mass : Fin n → ℝ
  /-- difficulty threshold of each group -/
  thr : Fin n → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  mass_sum : ∑ i, mass i = 1

/-- Accuracy of the population at boundary gate value `γ`. -/
noncomputable def ItemPopulation.acc (P : ItemPopulation) (γ : ℝ) : ℝ :=
  ∑ i, if P.thr i ≤ γ then P.mass i else 0


/-! ## The saturating boundary gate -/

/-- The saturating boundary gate: the exclusive block's coefficients are summed,
rectified and clipped at `1`.  Rectification makes it sign-sensitive, clipping
makes it redundant. -/
noncomputable def satGate {k : ℕ} (c : Fin k → ℝ) : ℝ := min (max (∑ i, c i) 0) 1





/-! ## Gate values of the six s = 13 interventions at `c = ![1, 1]` -/

/-- The control coefficient vector of the realisation: both exclusive
coordinates carry gain `1`, and the gate is already saturated at `1` — the
structural reason each single ablation is a no-op. -/
noncomputable def s13coef : Fin 2 → ℝ := ![1, 1]





/-! ## The s = 13 population -/

/-- Four difficulty groups tuned to the measured s = 13 length profile: 75.44 %
of the evaluation mass needs no boundary signal at all, 15.23 % needs a fifth of
it, 9.13 % needs half of it, and 0.20 % is never solved. -/
noncomputable def s13pop : ItemPopulation where
  n := 4
  mass := ![7544 / 10000, 1523 / 10000, 913 / 10000, 20 / 10000]
  thr := ![0, 1 / 5, 1 / 2, 2]
  mass_nonneg := by intro i; fin_cases i <;> norm_num
  mass_sum := by norm_num [Fin.sum_univ_succ]









/-! ## The missing middle, sharp -/



/-! ## Why the failed arms are no-ops in every intervention

Pooled over all twelve `k = 1` arms of NET-29 and NET-30, removal of the sole
exclusive coordinate is a no-op *in every arm where the model had already
failed*.  In the population model this is forced: an arm whose accuracy is
already the boundary-free accuracy `acc 0` has no gate-dependent mass among the
items it solves, so weakening the gate — by ablation, by a partial ablation, or
by rescaling — cannot cost anything. -/







/-! ## Part B: the k = 1 rows constrain nothing -/


end NumberTheory.ExclusiveChannel


