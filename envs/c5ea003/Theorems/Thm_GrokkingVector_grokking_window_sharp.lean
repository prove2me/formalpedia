-- Prove2me | Theorems.Thm_GrokkingVector_grokking_window_sharp
-- name    : GrokkingVector.grokking_window_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:05:20.136327+00:00
-- url     : https://prove2.me/theorems/0b19ed87-0d8f-4b38-8df6-66fab41aacce
-- title:
--   The training set of the example is *not* perfectly classified before time
-- statement:
--   The training set of the example is *not* perfectly classified before time
--   `1/2`, and the test point *is* classified correctly after time `2`: the window
--   above is sharp on both sides.
--
--   ```lean
--   theorem GrokkingVector.grokking_window_sharp:
--       (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → ¬ TrainPerfect t) ∧
--         (∀ t : ℝ, 2 < t → TestCorrect t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/VectorMargin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/VectorMargin.lean#L371

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



/-! ### Worst-case margin over a finite test set -/







/-! ### Vector-valued two-layer ReLU networks -/















/-! ### Delayed positivity of the classification margin -/



/-! ### An explicit train/test separation window -/

theorem GrokkingVector.grokking_window_sharp:
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → ¬ TrainPerfect t) ∧
      (∀ t : ℝ, 2 < t → TestCorrect t) := by sorry
