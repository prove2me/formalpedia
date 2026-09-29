-- Prove2me | solution 1 for AttentionCostLaw.attention_cost_law
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:42:04.869831+00:00
-- url     : https://prove2.me/submissions/60799cf7-6825-443d-890b-642270dafae4

-- Sol generated from Probability/AttentionCostLaw.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Definitions.Def_Probability_AttentionCostLaw
import Theorems.Thm_AttentionCostLaw_kStar_isLeast
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






/-!
## 3.  Uniqueness: the two qualitative findings already force the form
-/




/-!
## 4.  Capstone: end-to-end guarantee at the law's budget
-/


/-!
## 5.  Stability of the measured knee, and the NET-36 lab notes
-/












open AttentionCostLaw in
theorem solution{A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hcal : A / δ = 1 / 32) {d ctx : ℕ} (hd : 0 < d) (hctx : 0 < ctx)
    (hdvd : 32 ∣ d * ctx) :
    IsLeast {k : ℕ | 0 < k ∧ (d : ℝ) * zipfTail A ctx k ≤ δ} (d * ctx / 32) := by
  have hctxR : (0 : ℝ) < ctx := by exact_mod_cast hctx
  have key : A * d * ctx / δ = ((d * ctx / 32 : ℕ) : ℝ) := by
    obtain ⟨m, hm⟩ := hdvd
    have hnat : d * ctx / 32 = m := by omega
    have hcast : ((d : ℝ)) * ctx = 32 * m := by
      have : ((d * ctx : ℕ) : ℝ) = ((32 * m : ℕ) : ℝ) := by rw [hm]
      push_cast at this
      linarith
    rw [hnat]
    have : A * d * ctx / δ = (A / δ) * ((d : ℝ) * ctx) := by field_simp
    rw [this, hcal, hcast]
    ring
  have := kStar_isLeast (A := A) (ctx := (ctx : ℝ)) (δ := δ) (d := d) hA hctxR hδ hd
  rwa [key, Nat.ceil_natCast] at this
