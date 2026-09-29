-- Prove2me | solution 1 for GrokkingVector.delay_upper_bound_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:14:55.04567+00:00
-- url     : https://prove2.me/submissions/20d4cd64-882a-4220-a605-ee0748b4d807

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


theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_right _ _

theorem le_relu (x : ℝ) : x ≤ relu x := le_max_left _ _












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





/-! ### Robustness of the delayed transition -/


/-! ### The grokking ratio can be made arbitrarily large -/





open GrokkingVector in
theorem solution{m d : ℕ} (W : Fin m → Fin d → ℝ)
    (b a : Fin m → ℝ) (c : ℝ) (p : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j) {j₀ : Fin m}
    (ha₀ : 0 < a j₀) (hs₀ : 0 < signal W p j₀) {tau : ℝ}
    (hbefore : ∀ t ≤ tau, netRamp W b a c p t ≤ 0) :
    tau ≤ (-c / a j₀ - b j₀) / signal W p j₀ := by
  by_contra hcon
  push_neg at hcon
  set T : ℝ := (-c / a j₀ - b j₀) / signal W p j₀ with hT
  have hTs : T * signal W p j₀ = -c / a j₀ - b j₀ := by
    rw [hT]; exact div_mul_cancel₀ _ (ne_of_gt hs₀)
  set T' : ℝ := (T + tau) / 2 with hT'
  have hTT' : T < T' := by simp only [hT']; linarith
  have hT'tau : T' ≤ tau := by simp only [hT']; linarith
  have hle := hbefore T' hT'tau
  rw [netRamp_eq] at hle
  have hstrict : -c / a j₀ < T' * signal W p j₀ + b j₀ := by
    have := mul_lt_mul_of_pos_right hTT' hs₀
    have hval : T * signal W p j₀ + b j₀ = -c / a j₀ := by rw [hTs]; ring
    linarith
  have hterm : -c < a j₀ * relu (T' * signal W p j₀ + b j₀) := by
    have h1 : -c / a j₀ < relu (T' * signal W p j₀ + b j₀) :=
      lt_of_lt_of_le hstrict (le_relu _)
    calc -c = a j₀ * (-c / a j₀) := by field_simp
      _ < a j₀ * relu (T' * signal W p j₀ + b j₀) := by
          exact mul_lt_mul_of_pos_left h1 ha₀
  have hsum : a j₀ * relu (T' * signal W p j₀ + b j₀)
      ≤ ∑ j, a j * relu (T' * signal W p j + b j) :=
    Finset.single_le_sum (f := fun j => a j * relu (T' * signal W p j + b j))
      (fun j _ => mul_nonneg (ha j) (relu_nonneg _)) (Finset.mem_univ j₀)
  linarith
