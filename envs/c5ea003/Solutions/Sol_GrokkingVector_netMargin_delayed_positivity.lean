-- Prove2me | solution 1 for GrokkingVector.netMargin_delayed_positivity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:10:01.130695+00:00
-- url     : https://prove2.me/submissions/33d2a765-d5d2-4b00-a3fa-0c97832aa8ae

-- Sol generated from MachineLearning/GrokkingDelayedTransition/VectorMargin.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin
import Theorems.Thm_GrokkingVector_exists_sharp_threshold
import Theorems.Thm_GrokkingVector_netRamp_eq
import Theorems.Thm_GrokkingVector_netRamp_eventually_pos
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

theorem margin_monotone {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ)
    (hg : ∀ k, Monotone (g k)) : Monotone (margin hn g) := by
  intro a b hab
  exact Finset.le_inf' _ _ fun k _ => le_trans (margin_le hn g a k) (hg k hab)

theorem margin_continuous {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ)
    (hg : ∀ k, Continuous (g k)) : Continuous (margin hn g) :=
  Continuous.finset_inf'_apply _ fun k _ => hg k

/-- **Delayed positivity of a worst-case margin.**  If every one of finitely many
signed scores is monotone, continuous and eventually positive, and at least one
of them starts negative, then the margin has a sharp threshold. -/
theorem margin_sharp_threshold {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ → ℝ)
    (hmono : ∀ k, Monotone (g k)) (hcont : ∀ k, Continuous (g k))
    (hneg : ∃ k, g k 0 < 0) (hpos : ∀ k, ∃ T, 0 < g k T) :
    ∃ tau : ℝ, 0 ≤ tau ∧
      (∀ t ≤ tau, margin hn g t ≤ 0) ∧ (∀ t, tau < t → 0 < margin hn g t) := by
  obtain ⟨k₀, hk₀⟩ := hneg
  choose Tk hTk using hpos
  set T : ℝ := (Finset.univ : Finset (Fin n)).sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)) Tk with hT
  refine exists_sharp_threshold (margin hn g) (margin_monotone hn g hmono)
    (margin_continuous hn g hcont) (lt_of_le_of_lt (margin_le hn g 0 k₀) hk₀) ⟨T, ?_⟩
  refine lt_margin hn g T fun k => ?_
  exact lt_of_lt_of_le (hTk k) (hmono k (Finset.le_sup' Tk (Finset.mem_univ k)))

/-! ### Vector-valued two-layer ReLU networks -/





theorem relu_mono : Monotone relu := fun _ _ h => max_le_max h le_rfl





theorem netRamp_continuous {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) : Continuous (netRamp W b a c p) := by
  have h : netRamp W b a c p
      = fun t => c + ∑ j, a j * relu (t * signal W p j + b j) :=
    funext fun t => netRamp_eq W b a c p t
  rw [h]
  refine continuous_const.add (continuous_finset_sum _ fun j _ => ?_)
  exact continuous_const.mul (((continuous_id.mul continuous_const).add
    continuous_const).max continuous_const)

/-- With nonnegative output weights and nonnegative signals the ramped network
output is monotone in the ramp parameter. -/
theorem netRamp_monotone {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j) (hsig : ∀ j, 0 ≤ signal W p j) :
    Monotone (netRamp W b a c p) := by
  intro t₁ t₂ ht
  simp only [netRamp_eq]
  have hsum : ∑ j, a j * relu (t₁ * signal W p j + b j)
      ≤ ∑ j, a j * relu (t₂ * signal W p j + b j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (relu_mono ?_) (ha j)
    have := mul_le_mul_of_nonneg_right ht (hsig j)
    linarith
  linarith


/-- At ramp `0` a network with nonpositive hidden biases outputs its output
bias. -/
theorem netRamp_zero {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (hb : ∀ j, b j ≤ 0) : netRamp W b a c p 0 = c := by
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      a j * relu (0 * signal W p j + b j) = 0 := by
    intro j _
    have hle : 0 * signal W p j + b j ≤ 0 := by simpa using hb j
    rw [relu_of_nonpos hle, mul_zero]
  rw [netRamp_eq, Finset.sum_eq_zero h0, add_zero]


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
theorem solution{m d n : ℕ} (hn : 0 < n)
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
      (∀ t, tau < t → 0 < margin hn (signedScore W b a c p y) t) := by
  have hmono : ∀ k, Monotone (signedScore W b a c p y k) := by
    intro k
    rcases hlabel k with h1 | h1
    · intro t₁ t₂ ht
      simp only [signedScore, h1, one_mul]
      exact netRamp_monotone W b a c (p k) ha (hposdir k h1) ht
    · intro t₁ t₂ ht
      simp only [signedScore, h1]
      have hsame : ∀ t : ℝ, netRamp W b a c (p k) t
          = c + ∑ j, a j * relu (t * signal W (p k) j + b j) := netRamp_eq W b a c (p k)
      -- for a negative-class point every unit stays silent for `t ≥ 0`,
      -- but monotonicity must hold for all `t`; we use that the score is
      -- antitone in `t` since all signals are nonpositive
      have hanti : netRamp W b a c (p k) t₂ ≤ netRamp W b a c (p k) t₁ := by
        rw [hsame t₁, hsame t₂]
        have hsum : ∑ j, a j * relu (t₂ * signal W (p k) j + b j)
            ≤ ∑ j, a j * relu (t₁ * signal W (p k) j + b j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul_of_nonneg_left (relu_mono ?_) (ha j)
          have hsig := hneg k h1 j
          nlinarith
        linarith
      nlinarith
  have hcont : ∀ k, Continuous (signedScore W b a c p y k) := by
    intro k
    exact continuous_const.mul (netRamp_continuous W b a c (p k))
  have hpos : ∀ k, ∃ T, 0 < signedScore W b a c p y k T := by
    intro k
    rcases hlabel k with h1 | h1
    · obtain ⟨j₀, ha₀, hs₀⟩ := hactive k h1
      obtain ⟨T, hT⟩ := netRamp_eventually_pos W b a c (p k) ha ha₀ hs₀
      exact ⟨T, by simp only [signedScore, h1, one_mul]; exact hT⟩
    · refine ⟨0, ?_⟩
      simp only [signedScore, h1]
      rw [netRamp_zero W b a c (p k) hb]
      linarith
  obtain ⟨k₁, hk₁⟩ := hexists_pos
  have hstart : signedScore W b a c p y k₁ 0 < 0 := by
    simp only [signedScore, hk₁, one_mul]
    rw [netRamp_zero W b a c (p k₁) hb]
    exact hc
  exact margin_sharp_threshold hn _ hmono hcont ⟨k₁, hstart⟩ hpos
