-- Prove2me | Theorems.Thm_GrokkingVector_exists_sharp_threshold
-- name    : GrokkingVector.exists_sharp_threshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:04:17.565462+00:00
-- url     : https://prove2.me/theorems/6f2ee59b-898d-4c94-8cb3-e102f2a9a3b0
-- title:
--   Sharp threshold.
-- statement:
--   **Sharp threshold.**  A monotone continuous function that is negative at `0`
--   and eventually positive has a threshold `τ ≥ 0` with `f ≤ 0` on `(-∞, τ]` and
--   `f > 0` on `(τ, ∞)`.
--
--   ```lean
--   theorem GrokkingVector.exists_sharp_threshold(f : ℝ → ℝ) (hmono : Monotone f) (hcont : Continuous f)
--       (h0 : f 0 < 0) (hT : ∃ T, 0 < f T) :
--       ∃ tau : ℝ, 0 ≤ tau ∧ (∀ t ≤ tau, f t ≤ 0) ∧ (∀ t, tau < t → 0 < f t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/VectorMargin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/VectorMargin.lean#L35

-- Thm stub generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin

/-!
# Delayed margin positivity for vector-valued two-layer ReLU networks

The catalog file `Catalog/MachineLearning/GrokkingPhaseTransition.lean` treats a
width-one *scalar* network.  This file carries out Future Direction 1 (finite
hidden width, matrix weights, a finite test set, and a classification margin)
and Direction 3 (train/test separation).

Main results.

* `exists_sharp_threshold`: any monotone continuous signal that starts negative
  and is eventually positive has a *sharp* threshold `τ`: it is `≤ 0` on
  `(-∞, τ]` and `> 0` on `(τ, ∞)`.  The threshold is unique
  (`sharp_threshold_unique`).
* `margin_sharp_threshold`: the same holds for the *minimum* over a finite test
  set of finitely many such signals — the delayed transition survives taking a
  worst-case margin over a test set.
* `netMargin_delayed_positivity`: for a genuinely vector-valued two-layer ReLU
  network (hidden width `m`, input dimension `d`, matrix weights, negative
  output bias, a finite two-class test set) the classification margin is
  nonpositive up to an explicit delay and strictly positive afterwards.
* `grokking_window_eq`: for a concrete dataset the set of times at which the
  training set is already perfectly classified while the test point is still
  misclassified is *exactly* the interval `(1/2, 2]` — a formal train/test
  separation window.
-/

open GrokkingVector

open Finset Set

/-! ### Sharp thresholds for monotone continuous signals -/

theorem GrokkingVector.exists_sharp_threshold(f : ℝ → ℝ) (hmono : Monotone f) (hcont : Continuous f)
    (h0 : f 0 < 0) (hT : ∃ T, 0 < f T) :
    ∃ tau : ℝ, 0 ≤ tau ∧ (∀ t ≤ tau, f t ≤ 0) ∧ (∀ t, tau < t → 0 < f t) := by sorry
