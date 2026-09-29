-- Prove2me | solution 1 for GrokkingVector.delay_lower_bound_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:14:54.202983+00:00
-- url     : https://prove2.me/submissions/fd16b883-376c-4802-9bbb-53db444e3a32

-- Sol generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin
import Theorems.Thm_GrokkingVector_netRamp_eq

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

/-- With nonpositive hidden biases the ramped output is dominated by its
linearization at nonnegative ramp times. -/
theorem netRamp_le_linear {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 0)
    (hsig : ∀ j, 0 ≤ signal W p j) {t : ℝ} (ht : 0 ≤ t) :
    netRamp W b a c p t ≤ c + t * ∑ j, a j * signal W p j := by
  have hlin : ∑ j, a j * (t * signal W p j) = t * ∑ j, a j * signal W p j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ j, a j * relu (t * signal W p j + b j)
      ≤ ∑ j, a j * (t * signal W p j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left
      (max_le (by linarith [hb j]) (mul_nonneg ht (hsig j))) (ha j)
  rw [netRamp_eq, ← hlin]
  linarith




/-! ### Robustness of the delayed transition -/


/-! ### The grokking ratio can be made arbitrarily large -/





open GrokkingVector in
theorem solution{m d : ℕ} (W : Fin m → Fin d → ℝ)
    (b a : Fin m → ℝ) (c : ℝ) (p : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 0)
    (hsig : ∀ j, 0 ≤ signal W p j)
    (hc : c < 0) (hS : 0 < ∑ j, a j * signal W p j) {tau : ℝ}
    (hafter : ∀ t, tau < t → 0 < netRamp W b a c p t) :
    -c / (∑ j, a j * signal W p j) ≤ tau := by
  set S : ℝ := ∑ j, a j * signal W p j with hSdef
  by_contra hcon
  push_neg at hcon
  have hbound : 0 < -c / S := div_pos (by linarith) hS
  set t : ℝ := max tau 0 + (-c / S - max tau 0) / 2 with htdef
  have hmaxlt : max tau 0 < -c / S := max_lt hcon hbound
  have ht1 : tau < t := by
    have h1 : tau ≤ max tau 0 := le_max_left _ _
    have h2 : 0 < (-c / S - max tau 0) / 2 := by linarith
    linarith
  have ht0 : 0 ≤ t := by
    have h1 : (0 : ℝ) ≤ max tau 0 := le_max_right _ _
    have h2 : 0 < (-c / S - max tau 0) / 2 := by linarith
    linarith
  have ht2 : t < -c / S := by
    have h2 : 0 < (-c / S - max tau 0) / 2 := by linarith
    simp only [htdef]
    linarith
  have hpos := hafter t ht1
  have hle := netRamp_le_linear W b a c p ha hb hsig ht0
  have hlin : c + t * S < 0 := by
    have : t * S < -c := by
      rw [lt_div_iff₀ hS] at ht2
      linarith
    linarith
  linarith
