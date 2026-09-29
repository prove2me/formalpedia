-- Prove2me | Theorems.Thm_AttentionCostLaw_speedup_context_invariant
-- name    : AttentionCostLaw.speedup_context_invariant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:58:21.301183+00:00
-- url     : https://prove2.me/theorems/e6a3ff7e-54a9-4d78-9791-6d05af8d12b5
-- title:
--   Context-invariant speedup.
-- statement:
--   **Context-invariant speedup.**  On a cell obeying the law, the attention
--   speedup `ctx/k*` equals `32/d` — it does not depend on the context length.  This
--   is the deployable lever the grid reports (`8×` at `d = 4`).
--
--   ```lean
--   theorem AttentionCostLaw.speedup_context_invariant{d ctx : ℕ} (hd : 0 < d) (hctx : 0 < ctx)
--       (hdvd : 32 ∣ d * ctx) :
--       ((ctx : ℝ)) / ((d * ctx / 32 : ℕ) : ℝ) = 32 / d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionCostLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionCostLaw.lean#L173

-- Thm stub generated from Probability/AttentionCostLaw.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Definitions.Def_Probability_AttentionCostLaw
/-
# A derivation of the attention-cost law `k* = d · ctx / 32`

Round NET-36 completes a two-seed `(depth × context)` grid for the empirical law

  `k*(d, ctx) = d · ctx / 32`,

where `k*` is the smallest top-`k` attention budget retaining `≥ 0.98` of the full
model's held-out accuracy.  Measured cells: `k* = 16, 32, 64` at `d = 4, 8, 16`
(`ctx = 128`) and `k* = 64` at `d = 4, ctx = 512`, each at two seeds.

`AttentionConcentration.lean` shows the law is *not* a consequence of the measured
concentration statistic.  This file supplies a mechanism that does produce it, and
proves the mechanism is essentially the only one compatible with the two
qualitative facts the grid reports (linear depth scaling, context-invariant
speedup).

Main results.

* `AttentionCostLaw.layerComp_dist_le` : end-to-end deviation of a stack of `d`
  nonexpansive layers, each perturbed by at most `ε i`, is at most `∑ ε i`
  (`layerComp_dist_le_uniform` : `d · ε` in the uniform case).  This is the
  *depth leg*: an end-to-end budget `δ` forces a per-layer budget `δ/d`.
* `AttentionCostLaw.zipf_feasible_iff` : under a Zipf tail
  `tail(k) = A · ctx / k` — the *context leg*, a scale-free attention profile —
  the budget `k` is sufficient iff `k ≥ A·d·ctx/δ`.
* `AttentionCostLaw.kStar_isLeast` : hence the optimal budget is exactly
  `⌈A·d·ctx/δ⌉₊`, and `AttentionCostLaw.attention_cost_law` : with the calibrated
  ratio `A/δ = 1/32` and `32 ∣ d·ctx`, exactly `d·ctx/32` — the measured law.
* `AttentionCostLaw.speedup_context_invariant` : the resulting speedup is `32/d`,
  independent of `ctx`.
* `AttentionCostLaw.cost_law_unique` : conversely, *any* cost law with a
  context-invariant speedup and a linear depth leg is `K(d,ctx) = d·ctx·K(1,1)`.
  So the grid's two qualitative findings already pin the functional form, and the
  single fitted constant `1/32` is the whole content of the calibration.
* `AttentionCostLaw.zipf_profile_forced` : and the Zipf profile itself is forced —
  among scale-free tail profiles it is the unique one whose knee is linear in
  depth.  So the mechanism, not just the functional form, is pinned by the grid.
* `AttentionCostLaw.truncation_end_to_end` : the capstone — Zipf tail plus
  nonexpansive layers gives an end-to-end guarantee at budget `d·ctx/32`.
* `AttentionCostLaw.knee_stability` and the two lab-note corollaries
  `netA_knee_seed_stable`, `netB_knee_seed_stable` : the measured knee is a
  *stable* functional of the sweep.  Cell A (`d=16, ctx=128`) tolerates seed
  perturbations up to `η = 0.005`, cell B (`d=4, ctx=512`) up to `η = 0.003`;
  the reported seed-to-seed spread is `±0.002`, strictly inside both margins.
  This is the formal content of "the grid is two-seed everywhere": with the
  measured margins, no seed could have moved either knee.
-/


open AttentionCostLaw

open Finset Filter Topology

/-!
## 1.  The depth leg: error accumulation through a stack of layers
-/

variable {X : Type*}






/-!
## 2.  The context leg: a scale-free (Zipf) attention tail
-/

theorem AttentionCostLaw.speedup_context_invariant{d ctx : ℕ} (hd : 0 < d) (hctx : 0 < ctx)
    (hdvd : 32 ∣ d * ctx) :
    ((ctx : ℝ)) / ((d * ctx / 32 : ℕ) : ℝ) = 32 / d := by sorry
