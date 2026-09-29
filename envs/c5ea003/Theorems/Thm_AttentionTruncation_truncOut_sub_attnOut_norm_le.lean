-- Prove2me | Theorems.Thm_AttentionTruncation_truncOut_sub_attnOut_norm_le
-- name    : AttentionTruncation.truncOut_sub_attnOut_norm_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:00:08.057686+00:00
-- url     : https://prove2.me/theorems/cdce211a-94e3-4abc-85a3-249bbfee0acf
-- title:
--   Read-out error of top-`k` truncation.
-- statement:
--   **Read-out error of top-`k` truncation.**  Renormalised truncation to a set
--   `T` carrying mass `ρ` moves the attention output by at most `2(1-ρ)·B`, where `B`
--   bounds the value vectors.  Renormalisation contributes `(1-ρ)B` and the dropped
--   tail contributes `(1-ρ)B`.
--
--   ```lean
--   theorem AttentionTruncation.truncOut_sub_attnOut_norm_le(s T : Finset ι) (hT : T ⊆ s) (p : ι → ℝ)
--       (v : ι → V) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) {B : ℝ}
--       (hB : ∀ i ∈ s, ‖v i‖ ≤ B) (hρ : 0 < ∑ i ∈ T, p i) :
--       ‖truncOut T p v - attnOut s p v‖ ≤ 2 * (1 - ∑ i ∈ T, p i) * B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionTruncationOutput.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionTruncationOutput.lean#L61

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

theorem AttentionTruncation.truncOut_sub_attnOut_norm_le(s T : Finset ι) (hT : T ⊆ s) (p : ι → ℝ)
    (v : ι → V) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) {B : ℝ}
    (hB : ∀ i ∈ s, ‖v i‖ ≤ B) (hρ : 0 < ∑ i ∈ T, p i) :
    ‖truncOut T p v - attnOut s p v‖ ≤ 2 * (1 - ∑ i ∈ T, p i) * B := by sorry
