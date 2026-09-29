-- Prove2me | Theorems.Thm_AttentionTruncation_topk_preserves_prediction
-- name    : AttentionTruncation.topk_preserves_prediction
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:59:32.906978+00:00
-- url     : https://prove2.me/theorems/21a3f3ea-02e2-45a9-97f9-00ebfb90dc22
-- title:
--   Top-`k` truncation preserves the prediction.
-- statement:
--   **Top-`k` truncation preserves the prediction.**  If the read-out map is
--   `L`-Lipschitz in the attention output and the exact logit margin at the predicted
--   class exceeds `4·L·(1-ρ)·B`, then the truncated model predicts the same class.
--   The requirement involves the retained mass only through `1-ρ`, scaled by the
--   margin — not through the `0.98` mass threshold.
--
--   ```lean
--   theorem AttentionTruncation.topk_preserves_prediction{C : Type*} (s T : Finset ι) (hT : T ⊆ s)
--       (p : ι → ℝ) (v : ι → V) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
--       {B : ℝ} (hB : ∀ i ∈ s, ‖v i‖ ≤ B) (hρ : 0 < ∑ i ∈ T, p i)
--       (score : V → C → ℝ) {L : ℝ} (hL : 0 ≤ L)
--       (hLip : ∀ y y' j, |score y j - score y' j| ≤ L * ‖y - y'‖)
--       (c : C)
--       (hmargin : ∀ j, j ≠ c →
--         score (attnOut s p v) j + 4 * L * (1 - ∑ i ∈ T, p i) * B
--           < score (attnOut s p v) c) :
--       ∀ j, j ≠ c → score (truncOut T p v) j < score (truncOut T p v) c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionTruncationOutput.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionTruncationOutput.lean#L130

-- Thm stub generated from Probability/AttentionTruncationOutput.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Definitions.Def_Probability_AttentionTruncationOutput
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

theorem AttentionTruncation.topk_preserves_prediction{C : Type*} (s T : Finset ι) (hT : T ⊆ s)
    (p : ι → ℝ) (v : ι → V) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    {B : ℝ} (hB : ∀ i ∈ s, ‖v i‖ ≤ B) (hρ : 0 < ∑ i ∈ T, p i)
    (score : V → C → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ y y' j, |score y j - score y' j| ≤ L * ‖y - y'‖)
    (c : C)
    (hmargin : ∀ j, j ≠ c →
      score (attnOut s p v) j + 4 * L * (1 - ∑ i ∈ T, p i) * B
        < score (attnOut s p v) c) :
    ∀ j, j ≠ c → score (truncOut T p v) j < score (truncOut T p v) c := by sorry
