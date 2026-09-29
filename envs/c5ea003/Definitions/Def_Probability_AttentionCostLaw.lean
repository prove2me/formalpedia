-- Prove2me | Definitions.Def_Probability_AttentionCostLaw
-- name    : Probability_AttentionCostLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:12.984983+00:00
-- url     : https://prove2.me/theorems/49c8697a-65d7-4b3a-8ffd-0c4e4b05a9f0
-- title:
--   Aether Catalog definitions — Probability_AttentionCostLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AttentionCostLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AttentionCostLaw.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
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


namespace AttentionCostLaw

open Finset Filter Topology

/-!
## 1.  The depth leg: error accumulation through a stack of layers
-/

variable {X : Type*}

/-- `layerComp f d` is the composite `f (d-1) ∘ ⋯ ∘ f 0` of the first `d` layers. -/
def layerComp (f : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | (n + 1) => fun x => f n (layerComp f n x)





/-!
## 2.  The context leg: a scale-free (Zipf) attention tail
-/

/-- Mass left outside the top `k` positions of a row over `ctx` positions, under
the scale-free hypothesis `tail(k) = A · ctx / k` (equivalently `tail` depends on
`k` only through `k/ctx`, with a `1/x` profile). -/
noncomputable def zipfTail (A ctx : ℝ) (k : ℕ) : ℝ := A * ctx / k





/-!
## 3.  Uniqueness: the two qualitative findings already force the form
-/




/-!
## 4.  Capstone: end-to-end guarantee at the law's budget
-/


/-!
## 5.  Stability of the measured knee, and the NET-36 lab notes
-/


/-- Swept budgets of NET-36 cell A (`d = 16`, `ctx = 128`). -/
def gridA : Finset ℕ := {8, 16, 32, 64, 96, 128}

/-- Measured retained-accuracy curve, NET-36 cell A (`d = 16`, `ctx = 128`,
seed 1): `8 → 0.858, 16 → 0.922, 32 → 0.970, 64 → 0.996, 96 → 0.999,
128 → 1.000`. -/
noncomputable def netA : ℕ → ℝ := fun k =>
  if k ≤ 8 then 0.858 else
  if k ≤ 16 then 0.922 else
  if k ≤ 32 then 0.970 else
  if k ≤ 64 then 0.996 else
  if k ≤ 96 then 0.999 else 1

/-- Swept budgets of NET-36 cell B (`d = 4`, `ctx = 512`). -/
def gridB : Finset ℕ := {16, 32, 64, 128, 256, 384}

/-- Measured retained-accuracy curve, NET-36 cell B (`d = 4`, `ctx = 512`,
seed 2): `16 → 0.965, 32 → 0.976, 64 → 0.985, 128 → 0.993, 256 → 0.998,
384 → 1.000`. -/
noncomputable def netB : ℕ → ℝ := fun k =>
  if k ≤ 16 then 0.965 else
  if k ≤ 32 then 0.976 else
  if k ≤ 64 then 0.985 else
  if k ≤ 128 then 0.993 else
  if k ≤ 256 then 0.998 else 1






end AttentionCostLaw


