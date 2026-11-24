-- Prove2me | solution 1 for GrokkingNextCycle.hatNet_failure_set
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:50:54.856889+00:00
-- url     : https://prove2.me/submissions/2e967b75-7bc8-4d7f-848b-9cbe9f4434c0

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











/-! ### (N3) A sign-indefinite network that groks twice -/

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

theorem hatNet_eq_aux (t : ℝ) :
    hatNet t = -1 / 2 + (relu t - 2 * relu (t - 1) + relu (t - 2)) := by
  have hsig : ∀ j : Fin 3, signal hatW (fun _ : Fin 1 => (1 : ℝ)) j = 1 := by
    intro j; simp [signal, hatW]
  rw [hatNet, netRamp_eq_aux]
  rw [Fin.sum_univ_three]
  rw [hsig 0, hsig 1, hsig 2]
  have e0 : t * 1 + hatB 0 = t := by simp [hatB]
  have e1 : t * 1 + hatB 1 = t - 1 := by simp [hatB]; ring
  have e2 : t * 1 + hatB 2 = t - 2 := by simp [hatB, Matrix.cons_val]; ring
  rw [e0, e1, e2]
  simp [hatA, Matrix.cons_val]
  ring

theorem solution :
    {t : ℝ | hatNet t ≤ 0} = Iic (1 / 2 : ℝ) ∪ Ici (3 / 2 : ℝ) := by
  ext t
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, hatNet_eq_aux]
  rcases le_total t 0 with h0 | h0
  · rw [relu_of_nonpos_aux h0, relu_of_nonpos_aux (by linarith : t - 1 ≤ 0),
      relu_of_nonpos_aux (by linarith : t - 2 ≤ 0)]
    constructor
    · intro _; left; linarith
    · intro _; norm_num
  · have hr0 : relu t = t := max_eq_left h0
    rcases le_total t 1 with h1 | h1
    · rw [hr0, relu_of_nonpos_aux (by linarith : t - 1 ≤ 0),
        relu_of_nonpos_aux (by linarith : t - 2 ≤ 0)]
      constructor
      · intro h; left; linarith
      · rintro (h | h) <;> linarith
    · have hr1 : relu (t - 1) = t - 1 := max_eq_left (by linarith)
      rcases le_total t 2 with h2 | h2
      · rw [hr0, hr1, relu_of_nonpos_aux (by linarith : t - 2 ≤ 0)]
        constructor
        · intro h; right; linarith
        · rintro (h | h) <;> linarith
      · have hr2 : relu (t - 2) = t - 2 := max_eq_left (by linarith)
        rw [hr0, hr1, hr2]
        constructor
        · intro _; right; linarith
        · intro _; linarith

#print axioms solution
