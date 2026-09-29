-- Prove2me | solution 1 for AttentionTruncation.retention_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:50.029896+00:00
-- url     : https://prove2.me/submissions/4807e05d-14aa-4d58-8e5a-e5c3c4fd30f3

-- Sol generated from Probability/AttentionTruncationOutput.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Definitions.Def_Probability_AttentionTruncationOutput
import Theorems.Thm_AttentionTruncation_topk_preserves_prediction
/-
# Why the accuracy knee is cheaper than the mass knee

`AttentionConcentration.lean` proves an assumption-free obstruction: at the
measured effective support `N_eff = 152.11`, retaining `98 %` of the attention
*mass* costs `k ≥ 146`, yet the measured accuracy knee is `k* = 64`.  The two
numbers are not contradictory, but they force a mechanism: the retained *accuracy*
must be robust to a mass deficit that is far from negligible.

This file supplies that mechanism at the level of the attention read-out.  A
truncated-and-renormalised attention row moves the layer's output by at most
`2(1-ρ)·B` where `ρ` is the retained mass and `B` bounds the value vectors, and a
prediction survives any perturbation smaller than half its logit margin.  Together
they give a retention threshold `ρ > 1 - m/(4·L·B)` for preserving the arg-max —
a threshold governed by the *logit margin* `m`, not by the `0.98` mass level.  So
the accuracy knee is allowed to sit strictly below the mass knee, exactly as
measured, and the gap is predicted to close as the margin shrinks.

Main results.

* `AttentionTruncation.norm_weighted_sum_le` : `‖∑_{i∈U} p i • v i‖ ≤ (∑_{i∈U} p i)·B`.
* `AttentionTruncation.truncOut_sub_attnOut_norm_le` : the top-`k` read-out error
  `‖trunc − full‖ ≤ 2(1-ρ)B`; the factor `2` is the sum of the renormalisation
  inflation `(1-ρ)B` and the dropped tail `(1-ρ)B`.
* `AttentionTruncation.argmax_stable` : an arg-max survives any score perturbation
  below half its margin.
* `AttentionTruncation.topk_preserves_prediction` : the composite — prediction is
  preserved whenever `4·L·(1-ρ)·B` is below the logit margin.
* `AttentionTruncation.retention_threshold` : the resulting sufficient retention
  level `ρ > 1 - m/(4LB)`, which for a healthy margin is far below `0.98`.
-/


open AttentionTruncation

open Finset

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]









open AttentionTruncation in
theorem solution{C : Type*} (s T : Finset ι) (hT : T ⊆ s)
    (p : ι → ℝ) (v : ι → V) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    {B : ℝ} (hB : ∀ i ∈ s, ‖v i‖ ≤ B) (hρ : 0 < ∑ i ∈ T, p i)
    (score : V → C → ℝ) {L m : ℝ} (hL : 0 < L) (hBpos : 0 < B)
    (hLip : ∀ y y' j, |score y j - score y' j| ≤ L * ‖y - y'‖)
    (c : C)
    (hmargin : ∀ j, j ≠ c → score (attnOut s p v) j + m ≤ score (attnOut s p v) c)
    (hthr : 1 - m / (4 * L * B) < ∑ i ∈ T, p i) :
    ∀ j, j ≠ c → score (truncOut T p v) j < score (truncOut T p v) c := by
  set ρ : ℝ := ∑ i ∈ T, p i with hρdef
  have h4LB : 0 < 4 * L * B := by positivity
  have hlt : 4 * L * (1 - ρ) * B < m := by
    have h := (sub_lt_iff_lt_add.mp hthr)
    have h' : 1 - ρ < m / (4 * L * B) := by linarith
    have := (mul_lt_mul_of_pos_left h' h4LB)
    rw [mul_div_cancel₀ _ h4LB.ne'] at this
    linarith [this]
  refine topk_preserves_prediction s T hT p v hp hsum hB hρ score hL.le hLip c ?_
  intro j hj
  have := hmargin j hj
  linarith [hlt]
