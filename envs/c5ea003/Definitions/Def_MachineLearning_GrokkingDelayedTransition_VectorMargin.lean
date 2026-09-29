-- Prove2me | Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin
-- name    : MachineLearning_GrokkingDelayedTransition_VectorMargin
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:51:39.800732+00:00
-- url     : https://prove2.me/theorems/d9c48175-1d57-44fa-a4c7-8025f8962536
-- title:
--   Aether Catalog definitions — MachineLearning_GrokkingDelayedTransition_VectorMargin
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GrokkingDelayedTransition.VectorMargin`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean by skeleton subtraction
import Mathlib

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

namespace GrokkingVector

open Finset Set

/-! ### Sharp thresholds for monotone continuous signals -/



/-! ### Worst-case margin over a finite test set -/

/-- The worst-case (minimum) value over a finite test set of signed scores. -/
noncomputable def margin {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ) (t : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).inf'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)) (fun k => g k t)






/-! ### Vector-valued two-layer ReLU networks -/

/-- The rectifier. -/
noncomputable def relu (x : ℝ) : ℝ := max x 0





/-- A two-layer ReLU network with hidden width `m`, input dimension `d`, matrix
hidden weights `W`, hidden biases `b`, output weights `a` and output bias `c`. -/
noncomputable def net {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  c + ∑ j, a j * relu ((∑ i, W j i * x i) + b j)

/-- The signal of hidden unit `j` on the input direction `p`. -/
def signal {m d : ℕ} (W : Fin m → Fin d → ℝ) (p : Fin d → ℝ) (j : Fin m) : ℝ :=
  ∑ i, W j i * p i

/-- The network evaluated on the ramped input `t · p`. -/
noncomputable def netRamp {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (t : ℝ) : ℝ :=
  net W b a c (fun i => t * p i)







/-! ### Delayed positivity of the classification margin -/

/-- The signed score of test point `k`: positive exactly when the network
classifies `k` correctly. -/
noncomputable def signedScore {m d n : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ)
    (c : ℝ) (p : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  y k * netRamp W b a c (p k) t


/-! ### An explicit train/test separation window -/

/-- Concrete width-one, one-dimensional network used for the separation
-/
noncomputable def exNet (p : ℝ) (t : ℝ) : ℝ :=
  netRamp (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) (fun _ => 1) (-1)
    (fun _ : Fin 1 => p) t


/-- Training set: a positive point with strong signal `2` and a negative point
with signal `-1`.  Both are classified correctly as soon as `t > 1/2`. -/
def TrainPerfect (t : ℝ) : Prop := 0 < 1 * exNet 2 t ∧ 0 < (-1) * exNet (-1) t

/-- Test point: a positive point with weak signal `1/2`. -/
def TestCorrect (t : ℝ) : Prop := 0 < 1 * exNet (1 / 2 : ℝ) t




/-! ### A concrete instance: the hypotheses are satisfiable and the delay is exact

The general theorem `netMargin_delayed_positivity` is not vacuous: here is a
two-class test set on which all of its hypotheses hold, and for which the sharp
margin threshold can be computed exactly (it equals `1`).
-/

namespace Example

open GrokkingVector

/-- Hidden weight matrix of the example (width one, dimension one). -/
def exW : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- Hidden biases of the example. -/
def exB : Fin 1 → ℝ := fun _ => 0

/-- Output weights of the example. -/
def exA : Fin 1 → ℝ := fun _ => 1

/-- Two test points: a positive-class point in direction `+1` and a
negative-class point in direction `-1`. -/
def exP : Fin 2 → Fin 1 → ℝ := fun k _ => if k = 0 then 1 else -1

/-- Labels of the two test points. -/
def exY : Fin 2 → ℝ := fun k => if k = 0 then 1 else -1

/-- Signed scores of the example. -/
noncomputable def exSigned : Fin 2 → ℝ → ℝ := signedScore exW exB exA (-1) exP exY








end Example

end GrokkingVector

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

namespace GrokkingVector

open Finset Set

/-! ### Convexity: the tropical structure of the ramped output -/






/-! ### Quantitative bounds on the delay -/





/-! ### Robustness of the delayed transition -/


/-! ### The grokking ratio can be made arbitrarily large -/

/-- Single-unit ramped score with signal strength `s` and unit output bias. -/
noncomputable def unitScore (s t : ℝ) : ℝ := -1 + relu (t * s)



end GrokkingVector


