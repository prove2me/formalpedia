-- Prove2me | Theorems.Thm_GrokkingVector_Example_exMargin_threshold_one
-- name    : GrokkingVector.Example.exMargin_threshold_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:04:58.980717+00:00
-- url     : https://prove2.me/theorems/9f44216f-0124-4569-b3ce-4f31951e4909
-- title:
--   The exact delay of the example: the worst-case margin is nonpositive up to
-- statement:
--   The exact delay of the example: the worst-case margin is nonpositive up to
--   time `1` and strictly positive afterwards.
--
--   ```lean
--   theorem GrokkingVector.Example.exMargin_threshold_one:
--       (∀ t ≤ (1 : ℝ), margin (by norm_num : 0 < 2) exSigned t ≤ 0) ∧
--         (∀ t, (1 : ℝ) < t → 0 < margin (by norm_num : 0 < 2) exSigned t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/VectorMargin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/VectorMargin.lean#L454

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








/-! ### A concrete instance: the hypotheses are satisfiable and the delay is exact

The general theorem `netMargin_delayed_positivity` is not vacuous: here is a
two-class test set on which all of its hypotheses hold, and for which the sharp
margin threshold can be computed exactly (it equals `1`).
-/

open Example

open GrokkingVector

theorem GrokkingVector.Example.exMargin_threshold_one:
    (∀ t ≤ (1 : ℝ), margin (by norm_num : 0 < 2) exSigned t ≤ 0) ∧
      (∀ t, (1 : ℝ) < t → 0 < margin (by norm_num : 0 < 2) exSigned t) := by sorry
