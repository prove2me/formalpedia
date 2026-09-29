-- Prove2me | solution 1 for GrokkingVector.exists_sharp_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:06:12.842652+00:00
-- url     : https://prove2.me/submissions/e1e7f867-7919-4644-87b3-d811579277ec

-- Sol generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean
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
theorem solution(f : ℝ → ℝ) (hmono : Monotone f) (hcont : Continuous f)
    (h0 : f 0 < 0) (hT : ∃ T, 0 < f T) :
    ∃ tau : ℝ, 0 ≤ tau ∧ (∀ t ≤ tau, f t ≤ 0) ∧ (∀ t, tau < t → 0 < f t) := by
  obtain ⟨T, hTpos⟩ := hT
  set A : Set ℝ := {t : ℝ | f t ≤ 0} with hA
  have hAne : A.Nonempty := ⟨0, by simpa [hA] using h0.le⟩
  have hAbdd : BddAbove A := by
    refine ⟨T, fun a ha => ?_⟩
    by_contra hcon
    push_neg at hcon
    have : f T ≤ f a := hmono hcon.le
    have : f a ≤ 0 := ha
    linarith
  have hAclosed : IsClosed A := by
    have : A = f ⁻¹' (Iic 0) := rfl
    rw [this]
    exact IsClosed.preimage hcont isClosed_Iic
  have hmem : sSup A ∈ A := hAclosed.csSup_mem hAne hAbdd
  refine ⟨sSup A, le_csSup hAbdd (by simpa [hA] using h0.le), ?_, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · exact hmem
    · by_contra hcon
      push_neg at hcon
      have hub : ∀ a ∈ A, a ≤ t := by
        intro a ha
        by_contra hca
        push_neg at hca
        have : f t ≤ f a := hmono hca.le
        have : f a ≤ 0 := ha
        linarith
      have : sSup A ≤ t := csSup_le hAne hub
      linarith
  · intro t ht
    by_contra hcon
    push_neg at hcon
    have : t ∈ A := hcon
    have : t ≤ sSup A := le_csSup hAbdd this
    linarith
