-- Prove2me | Definitions.Def_Probability_AttentionTruncationOutput
-- name    : Probability_AttentionTruncationOutput
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:07.909787+00:00
-- url     : https://prove2.me/theorems/07725379-152c-4d55-97da-1365557f5da8
-- title:
--   Aether Catalog definitions — Probability_AttentionTruncationOutput
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AttentionTruncationOutput`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AttentionTruncationOutput.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
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


namespace AttentionTruncation

open Finset

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact attention read-out `∑ p i • v i`. -/
def attnOut (s : Finset ι) (p : ι → ℝ) (v : ι → V) : V := ∑ i ∈ s, p i • v i

/-- The top-`k` read-out: restrict the row to `T` and renormalise. -/
noncomputable def truncOut (T : Finset ι) (p : ι → ℝ) (v : ι → V) : V :=
  (∑ i ∈ T, p i)⁻¹ • ∑ i ∈ T, p i • v i






end AttentionTruncation


