-- Prove2me | solution 1 for GrokkingVector.Example.exMargin_threshold_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:14:53.47224+00:00
-- url     : https://prove2.me/submissions/8e35e74e-2268-44ec-aa8d-f1ccc469ec2e

-- Sol generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin
import Theorems.Thm_GrokkingVector_netRamp_eq
import Theorems.Thm_GrokkingVector_relu_of_nonpos

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


theorem margin_le {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ) (t : ℝ) (k : Fin n) :
    margin hn g t ≤ g k t :=
  Finset.inf'_le _ (Finset.mem_univ k)

theorem lt_margin {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ) (t : ℝ) {c : ℝ}
    (h : ∀ k, c < g k t) : c < margin hn g t :=
  (Finset.lt_inf'_iff _).mpr fun k _ => h k




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









theorem exSigned_zero (t : ℝ) : exSigned 0 t = -1 + relu t := by
  simp [exSigned, signedScore, netRamp_eq, signal, exW, exB, exA, exP, exY]

theorem exSigned_one (t : ℝ) : exSigned 1 t = 1 - relu (-t) := by
  simp [exSigned, signedScore, netRamp_eq, signal, exW, exB, exA, exP, exY]
  ring






/-!
# Quantitative delay bounds, convex (tropical) structure, and robustness

Second research cycle.  `VectorMargin.lean` proves that the worst-case margin of
a vector-valued two-layer ReLU network has a *sharp* delay `τ`.  Here we

* locate `τ` quantitatively: `delay_lower_bound_of_threshold` and
  `delay_upper_bound_of_threshold` sandwich the delay between `|c| / S`, where
  `S = ∑ⱼ aⱼ gⱼ` is the total signal of the point, and
  `(|c|/a_{j₀} - b_{j₀})/g_{j₀}` coming from any single active unit — so the
  delay scales like *output-bias magnitude divided by signal strength*;
* connect the delay to the *tropical / convex-geometric* picture of the catalog
  file `Catalog/Tropical/NeuralCoding/GrokPhaseTransition.lean`: the ramped
  network output is a convex piecewise-linear (tropical) function of the ramp
  parameter (`netRamp_convexOn`), hence the set of times at which the network
  still fails is always an interval (`failure_set_convex`) — the delayed
  transition can never happen twice;
* prove robustness of the delayed transition itself
  (`perturbed_delayed_transition`): a uniformly `ε`-close trajectory keeps the
  transition, with the threshold moving by at most `ε/κ` where `κ` is the growth
  rate after the threshold;
* prove that the ratio between test delay and train delay is unbounded
  (`grokking_ratio_unbounded`): weakening the test signal makes the grokking
  window arbitrarily long compared with the time to fit the training set.
-/

open GrokkingVector

open Finset Set

/-! ### Convexity: the tropical structure of the ramped output -/






/-! ### Quantitative bounds on the delay -/





/-! ### Robustness of the delayed transition -/


/-! ### The grokking ratio can be made arbitrarily large -/





open GrokkingVector in
theorem solution:
    (∀ t ≤ (1 : ℝ), margin (by norm_num : 0 < 2) exSigned t ≤ 0) ∧
      (∀ t, (1 : ℝ) < t → 0 < margin (by norm_num : 0 < 2) exSigned t) := by
  constructor
  · intro t ht
    refine le_trans (margin_le _ exSigned t 0) ?_
    rw [exSigned_zero]
    have : relu t ≤ 1 := max_le ht zero_le_one
    linarith
  · intro t ht
    refine lt_margin _ exSigned t (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [exSigned_zero]
      have h : relu t = t := max_eq_left (by linarith)
      rw [h]; linarith
    · rw [exSigned_one]
      have h : relu (-t) = 0 := relu_of_nonpos (by linarith)
      rw [h]; norm_num
