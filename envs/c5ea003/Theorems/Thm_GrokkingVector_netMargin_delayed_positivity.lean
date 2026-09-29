-- Prove2me | Theorems.Thm_GrokkingVector_netMargin_delayed_positivity
-- name    : GrokkingVector.netMargin_delayed_positivity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:04:28.454885+00:00
-- url     : https://prove2.me/theorems/338b22b8-b3fb-441e-8477-899750a3020f
-- title:
--   **Delayed positivity of the classification margin for a vector-valued
-- statement:
--   **Delayed positivity of the classification margin for a vector-valued
--   two-layer ReLU network.**
--
--   Data: hidden width `m`, input dimension `d`, matrix hidden weights `W`,
--   nonpositive hidden biases, nonnegative output weights, a strictly negative
--   output bias `c`, and a finite test set of `n` labelled points presented through
--   a ramp `t ↦ t·p k`.  Negative-class points (`y k = -1`) leave every hidden unit
--   silent, positive-class points (`y k = 1`) excite at least one hidden unit.
--
--   Conclusion: the worst-case margin over the test set is `≤ 0` up to an explicit
--   threshold `τ ≥ 0` and strictly positive after it.
--
--   ```lean
--   theorem GrokkingVector.netMargin_delayed_positivity{m d n : ℕ} (hn : 0 < n)
--       (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
--       (p : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
--       (hc : c < 0) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 0)
--       (hlabel : ∀ k, y k = 1 ∨ y k = -1)
--       (hneg : ∀ k, y k = -1 → ∀ j, signal W (p k) j ≤ 0)
--       (hposdir : ∀ k, y k = 1 → ∀ j, 0 ≤ signal W (p k) j)
--       (hactive : ∀ k, y k = 1 → ∃ j₀, 0 < a j₀ ∧ 0 < signal W (p k) j₀)
--       (hexists_pos : ∃ k, y k = 1) :
--       ∃ tau : ℝ, 0 ≤ tau ∧
--         (∀ t ≤ tau, margin hn (signedScore W b a c p y) t ≤ 0) ∧
--         (∀ t, tau < t → 0 < margin hn (signedScore W b a c p y) t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/VectorMargin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/VectorMargin.lean#L252

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

theorem GrokkingVector.netMargin_delayed_positivity{m d n : ℕ} (hn : 0 < n)
    (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin n → Fin d → ℝ) (y : Fin n → ℝ)
    (hc : c < 0) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 0)
    (hlabel : ∀ k, y k = 1 ∨ y k = -1)
    (hneg : ∀ k, y k = -1 → ∀ j, signal W (p k) j ≤ 0)
    (hposdir : ∀ k, y k = 1 → ∀ j, 0 ≤ signal W (p k) j)
    (hactive : ∀ k, y k = 1 → ∃ j₀, 0 < a j₀ ∧ 0 < signal W (p k) j₀)
    (hexists_pos : ∃ k, y k = 1) :
    ∃ tau : ℝ, 0 ≤ tau ∧
      (∀ t ≤ tau, margin hn (signedScore W b a c p y) t ≤ 0) ∧
      (∀ t, tau < t → 0 < margin hn (signedScore W b a c p y) t) := by sorry
