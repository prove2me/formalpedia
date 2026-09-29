-- Prove2me | Definitions.Def_Bridges_TropicalSatakeRobustness
-- name    : Bridges_TropicalSatakeRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:07.734574+00:00
-- url     : https://prove2.me/theorems/26cb4128-d242-4401-81d7-0d836df21558
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakeRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakeRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakeRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Satake Robustness Bridge for GL₃ Score Maps

This file formalizes a quantitative robustness theorem for multiclass score maps
built from max-plus linear forms on finitely many tropical Satake coordinates.

The key results are:
1. **Weighted drift bound** (`linearScoreDiff_drift_bound`): coordinatewise perturbation
   control implies global score difference control.
2. **Binary margin robustness** (`binary_margin_robust`): strict margin exceeding twice
   the drift budget implies sign preservation.
3. **Multiclass argmax invariance** (`multiclass_robust_of_pairwise_margins`): pairwise
   margin separation certifies winner invariance under perturbation.
4. **GL₃ wrapper** (`gl3_tropical_satake_certified_robustness`): packages the abstract
   result with GL₃ tropical Satake interpretation.

## Mathematical Context

The GL₃ tropical Satake transform maps Hecke data to a finite-dimensional tropical
coordinate system indexed by dominant coweights. A "separating family" of such coordinates
determines the Hecke data completely. This file upgrades that qualitative reconstruction
principle to a quantitative certification principle: if a multiclass score map has
sufficient pairwise margin separation measured in these coordinates, then the predicted
class is stable under bounded perturbations of the input data.
-/


open Finset BigOperators

/-! ## Definitions -/

/-- Linear score difference: the inner product of coefficient vector `a` with coordinate
    vector `z`. This models pairwise score differences between classes in the tropical
    Satake coordinate system. -/
def LinearScoreDiff {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, a i * z i

/-- Weighted perturbation budget: the maximum change in `LinearScoreDiff a` when each
    coordinate `i` is perturbed by at most `eps i`. This equals `∑ i, |a i| * eps i`. -/
def DriftBudget {ι : Type*} [Fintype ι]
    (w eps : ι → ℝ) : ℝ :=
  ∑ i, |w i| * eps i

/-- A class `c` is a winner if its score is at least as large as every other class's score. -/
def IsWinner {κ : Type*} (score : κ → ℝ) (c : κ) : Prop :=
  ∀ c', score c' ≤ score c

/-! ## Section 1: Weighted Drift Bound -/

/-
**Core perturbation inequality.** The change in `LinearScoreDiff a` under coordinatewise
    perturbation bounded by `eps` is at most `DriftBudget a eps = ∑ i, |a i| * eps i`.

    This is the quantitative engine: it converts coordinatewise control of tropical Satake
    observables into global control of score differences.
-/

/-
**Affine margin lower bound.** If the original affine margin is `LinearScoreDiff a z + β`,
    then after perturbation bounded by `eps`, the new margin is at least the original minus
    the drift budget.
-/

/-! ## Section 2: Binary Robustness from Strict Margin -/

/-
**Binary margin robustness.** If the original pairwise margin `LinearScoreDiff a z + β`
    exceeds twice the drift budget, then the margin remains strictly positive after any
    perturbation bounded by `eps`. This is the "half-margin" phenomenon.
-/

/-
**Binary margin robustness (division form).** Equivalent formulation: if the drift budget
    is less than half the original margin, the margin's sign is preserved.
-/

/-! ## Section 3: Multiclass Argmax Invariance -/

/-
**Multiclass robustness from pairwise margins.** If class `c` has pairwise margin
    exceeding `2 * L c'` against every competitor `c'`, and the pairwise score difference
    drifts by at most `L c'` under perturbation, then `c` remains the winner.

    This is the core multiclass certification theorem. For each competitor `c' ≠ c`:
    ```
    score c z' - score c' z' ≥ (score c z - score c' z) - L c' > 2 * L c' - L c' = L c' ≥ 0
    ```
    hence `score c' z' ≤ score c z'`.
-/

/-
**Multiclass robustness with weighted drift budgets.** When pairwise score differences
    are linear (as in the tropical Satake coordinate model), the drift bound `L c'` is
    the weighted budget `DriftBudget (d c') eps`, and the margin condition becomes
    `2 * DriftBudget (d c') eps < LinearScoreDiff (d c') z + β c'`.

    This theorem directly links weighted coefficient presentations to multiclass robustness.
-/

/-! ## Section 4: GL₃ Tropical Satake Certified Robustness -/

/-
**GL₃ Tropical Satake Certified Robustness Theorem.**

    This is the main bridge theorem connecting tropical Satake geometry to certified
    robustness. Given:
    - A finite GL₃ separating coordinate family `phi : α → ι → ℝ`
    - Class scores depending only on these Satake coordinates
    - Coordinatewise perturbation bounds `eps`
    - Pairwise margin separation exceeding twice the Lipschitz drift

    The predicted class is invariant under perturbation.

    **Significance:** This upgrades finite determinacy of GL₃ tropical Satake data from
    a qualitative reconstruction principle to a quantitative certification principle. The
    separating coordinate family certifies stability of representation-theoretic tropical
    decisions under perturbation — the exact analogue of margin-based certified robustness
    for tropical/piecewise-linear classifiers, but in a genuinely non-neural decision class
    arising from tropical Langlands/Satake structure.
-/

/-
**GL₃ Robustness with explicit affine presentations.** A more explicit version where
    each pairwise margin is given by a linear score difference with known coefficients,
    allowing the Lipschitz bound to be derived automatically from `linearScoreDiff_drift_bound`.
-/


