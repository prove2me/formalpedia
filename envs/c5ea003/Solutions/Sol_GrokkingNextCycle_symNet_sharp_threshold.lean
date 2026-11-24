-- Prove2me | solution 1 for GrokkingNextCycle.symNet_sharp_threshold
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:50:53.698871+00:00
-- url     : https://prove2.me/submissions/1652c307-fd4a-4c0a-8d95-ded0cf4b2393

-- Thm stub generated from MachineLearning/GrokkingDelayedTransition/NextCycle.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_NextCycle
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin

/-!
# Closing the three next-cycle sub-conjectures of the grokking thread

`FUTURE_DIRECTIONS.md` of the previous cycle listed three concrete sub-conjectures
(N1)–(N3), and a sharpness half for Conjecture 4.  This file resolves all of
them, building directly on the definitions of
`GrokkingDelayedTransition/GradientFlowThreshold.lean` and
`GrokkingDelayedTransition/VectorMargin.lean`.

* **(N1) Filter-level divergence of the delay.**  `crossTime_tendsto_atTop`:
  the crossing time of the weight-decayed gradient flow tends to `+∞` as the
  weight decay increases to its critical value `λ_c = s/θ`.  This upgrades the
  purely existential `crossTime_diverges_at_criticality` to a genuine limit
  statement along the filter `𝓝[<] λ_c`.

* **(N2) An exact `1/m` width law.**  `zeroBias_sharp_threshold`: for a network
  with vanishing hidden biases the *sandwich* `delay_scaling_sandwich` collapses
  to an **equality**, the sharp delay being exactly `|c| / S` with
  `S = ∑ⱼ aⱼ gⱼ` the total signal.  Specialized to a symmetric width-`m`
  network (`symNet_sharp_threshold`) this gives `τ(m) = |c| / (m a g)`, hence
  the exact width law `m · τ(m) = |c|/(a g)` (`symNet_delay_width_law`) and
  `τ(m) → 0` (`symNet_delay_tendsto_zero`).

* **(N3) Grokking can happen twice.**  `hatNet_failure_set` computes the failure
  set of an explicit *sign-indefinite* width-three network to be exactly
  `(-∞, 1/2] ∪ [3/2, ∞)`, and `hatNet_failure_not_convex` shows it is not
  convex.  So the nonnegativity of the output weights in `netRamp_convexOn` /
  `failure_set_convex` cannot be dropped: with signed output weights a network
  can grok, un-grok and re-grok.

* **Sharpness of the robustness bound.**  `perturbed_threshold_shift_exact`:
  the displacement `ε/κ` of `perturbed_delayed_transition` is attained by the
  constant perturbation `-ε`, so that bound is sharp.
-/

open GrokkingNextCycle

open Filter Topology Set

/-! ### (N1) The delay diverges, as a limit along `𝓝[<] λ_c` -/


/-! ### (N2) An exact delay formula, and the `1/m` width law -/

-- open removed: section is not a namespace

open GrokkingVector

theorem netRamp_eq_aux {m d : ℕ} (W : Fin m → Fin d → ℝ) (b a : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (t : ℝ) :
    netRamp W b a c p t = c + ∑ j, a j * relu (t * signal W p j + b j) := by
  have hinner : ∀ j : Fin m, (∑ i, W j i * (t * p i)) = t * signal W p j := by
    intro j
    simp only [signal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [netRamp, net, hinner]

theorem relu_of_nonpos_aux {x : ℝ} (hx : x ≤ 0) : relu x = 0 := max_eq_right hx

theorem netRamp_zeroBias_eq_aux {m d : ℕ} (W : Fin m → Fin d → ℝ) (A : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (hsig : ∀ j, 0 ≤ signal W p j) {t : ℝ} (ht : 0 ≤ t) :
    netRamp W (fun _ => 0) A c p t = c + t * ∑ j, A j * signal W p j := by
  rw [netRamp_eq_aux, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnn : 0 ≤ t * signal W p j := mul_nonneg ht (hsig j)
  have : relu (t * signal W p j + 0) = t * signal W p j := by
    simp only [relu, add_zero]
    exact max_eq_left hnn
  rw [this]; ring

theorem netRamp_zeroBias_nonpos_aux {m d : ℕ} (W : Fin m → Fin d → ℝ) (A : Fin m → ℝ) (c : ℝ)
    (p : Fin d → ℝ) (hsig : ∀ j, 0 ≤ signal W p j) {t : ℝ} (ht : t ≤ 0) :
    netRamp W (fun _ => 0) A c p t = c := by
  rw [netRamp_eq_aux]
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      A j * relu (t * signal W p j + 0) = 0 := by
    intro j _
    have hle : t * signal W p j + 0 ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg ht (hsig j)
      linarith
    rw [relu_of_nonpos_aux hle, mul_zero]
  rw [Finset.sum_eq_zero h0, add_zero]

theorem zeroBias_sharp_threshold_aux {m d : ℕ} (W : Fin m → Fin d → ℝ) (A : Fin m → ℝ)
    (c : ℝ) (p : Fin d → ℝ) (hsig : ∀ j, 0 ≤ signal W p j) (hc : c < 0)
    (hS : 0 < ∑ j, A j * signal W p j) :
    (∀ t ≤ -c / (∑ j, A j * signal W p j), netRamp W (fun _ => 0) A c p t ≤ 0) ∧
      (∀ t, -c / (∑ j, A j * signal W p j) < t →
        0 < netRamp W (fun _ => 0) A c p t) := by
  set S : ℝ := ∑ j, A j * signal W p j with hSdef
  constructor
  · intro t ht
    rcases le_or_gt t 0 with h0 | h0
    · rw [netRamp_zeroBias_nonpos_aux W A c p hsig h0]; linarith
    · rw [netRamp_zeroBias_eq_aux W A c p hsig h0.le]
      have : t * S ≤ -c := by
        rw [le_div_iff₀ hS] at ht; linarith
      linarith
  · intro t ht
    have hpos : 0 < -c / S := div_pos (by linarith) hS
    have h0 : 0 < t := lt_trans hpos ht
    rw [netRamp_zeroBias_eq_aux W A c p hsig h0.le]
    have : -c < t * S := by
      rw [div_lt_iff₀ hS] at ht; linarith
    linarith

theorem symNet_signal_aux (m : ℕ) (g : ℝ) (j : Fin m) :
    signal (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ : Fin 1 => (1 : ℝ)) j = g := by
  simp [signal]

theorem symNet_totalSignal_aux (m : ℕ) (A g : ℝ) :
    ∑ _j : Fin m, A * g = (m : ℝ) * (A * g) := by
  simp [Finset.sum_const, nsmul_eq_mul]

theorem solution (m : ℕ) (A g c : ℝ) (hm : 0 < m) (hA : 0 < A)
    (hg : 0 < g) (hc : c < 0) :
    (∀ t ≤ symDelay m A g c, symNet m A g c t ≤ 0) ∧
      (∀ t, symDelay m A g c < t → 0 < symNet m A g c t) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsig : ∀ j : Fin m,
      0 ≤ signal (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ : Fin 1 => (1 : ℝ)) j := by
    intro j; rw [symNet_signal_aux]; exact hg.le
  have hsum : (∑ j : Fin m, (fun _ : Fin m => A) j *
      signal (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ : Fin 1 => (1 : ℝ)) j)
      = (m : ℝ) * (A * g) := by
    have : ∀ j : Fin m, (fun _ : Fin m => A) j *
        signal (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ : Fin 1 => (1 : ℝ)) j = A * g := by
      intro j; rw [symNet_signal_aux]
    rw [Finset.sum_congr rfl fun j _ => this j, symNet_totalSignal_aux]
  have hS : 0 < ∑ j : Fin m, (fun _ : Fin m => A) j *
      signal (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ : Fin 1 => (1 : ℝ)) j := by
    rw [hsum]; positivity
  have h := zeroBias_sharp_threshold_aux (fun _ : Fin m => fun _ : Fin 1 => g)
    (fun _ => A) c (fun _ : Fin 1 => 1) hsig hc hS
  rw [hsum] at h
  exact h

#print axioms solution
