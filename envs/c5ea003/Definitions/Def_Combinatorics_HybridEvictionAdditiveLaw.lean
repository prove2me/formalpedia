-- Prove2me | Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
-- name    : Combinatorics_HybridEvictionAdditiveLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:52.34254+00:00
-- url     : https://prove2.me/theorems/d0c26111-869e-4014-9d95-74eabed92351
-- title:
--   Aether Catalog definitions — Combinatorics_HybridEvictionAdditiveLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.HybridEvictionAdditiveLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/HybridEvictionAdditiveLaw.lean by skeleton subtraction
import Mathlib

/-!
# The additive-hybrid eviction law (NET-61: CONTENT-ADDITIVE-EVICTION-DOES-NOT-HELP)

This file formalises the *combinatorial* content behind the NET-61 measurement

> hybrid eviction score `= z(accumulated usage) + λ · z(static probe score)`,
> retained quality is **monotonically decreasing** in the probe weight `λ`,
> `λ = 0` is optimal, and every member of the family stays a fixed distance
> below the oracle at matched budget.

Measured table (Qwen2.5-0.5B, ctx = 1024):

| B   | λ    | retained |
|-----|------|----------|
| 64  | 0.00 | 0.9384   |
| 64  | 0.25 | 0.9383   |
| 64  | 1.00 | 0.9365   |
| 64  | 4.00 | 0.9344   |
| 32  | 1.00 | 0.9189   |
| 128 | 1.00 | 0.9544   |

The abstraction used here is the *cache-selection* one: a budget `B`, a cheap
score `s : ι → ℝ`, and the policy "keep a `B`-element set whose kept items all
score at least as high as every evicted item" (`IsTopSet`).  The quantity of
interest is the retained value `retained v S = ∑ i ∈ S, v i`, where `v` is the
(unavailable at run time) true future utility of a cache slot; the *oracle* is
the policy that scores with `v` itself.

The results:

* `sum_le_sum_of_sdiff_dominated` / `sum_lt_sum_of_sdiff_dominated` — the
  exchange kernel: a pairwise domination between the two symmetric differences
  of two equicardinal sets already orders their values (no matching/Hall
  argument is needed).
* `oracle_max`, `cheap_signal_le_oracle` — **the four-family bound**: *every*
  score function whatsoever, hence in particular accumulation, recency,
  content-probe and all their combinations, is dominated by the oracle at
  matched budget.  The gap is a property of the instance, not of the family.
* `probe_dominance_of_lambda_lt` — the **single-crossing lemma** for the
  additive family: if `λ₁ < λ₂` then every item that *enters* the cache when
  the probe weight is raised has probe score at least that of every item that
  *leaves*.  This is the structural reason a λ-sweep is monotone.
* `retained_antitone_in_lambda`, `retained_strictAnti_in_lambda` — the
  **monotone-degradation law** (P1 refuted): if the probe is anti-aligned with
  true utility, retained value is (strictly) decreasing in `λ`.
* `lambda_zero_optimal` — **P2 confirmed**: `λ = 0` maximises the family.
* `probeMass_monotone_in_lambda` / `usageMass_antitone_in_lambda` — the λ-sweep
  is a monotone trade-off path: probe mass up, usage mass down.
* `positive_lambda_can_strictly_help` — **sharpness**: without anti-alignment the
  law fails, so the measured degradation is a fact about the probe, not about
  additivity.
* `isTopSet_affine`, `zscore_hybrid_reparam`, `probe_constant_is_inert` —
  z-scoring is a *reparametrisation* of the same one-parameter policy family,
  so no claim here depends on the normalisation used in the experiment.
* `topSet_eq_initial_of_strictAnti` — a strictly ordered score forces the
  kept set, giving determinism of the measured arm.
* `net61_calibrated_gap` — a four-slot instance calibrated to the measured
  numbers: **for every `λ ≥ 0`** the hybrid retains exactly `0.9384` while the
  oracle retains `0.9954`, a gap of exactly `0.0570` (5.7 points).
* `oracle_retained_mono` — retained value is monotone in the budget `B`
  (the `32 < 64 < 128` rows), so budget, unlike probe weight, does help.
-/

namespace Catalog.Combinatorics.HybridEvictionAdditiveLaw

open Finset

section General

variable {ι : Type*} [DecidableEq ι]

/-- `S` is a set of `B` cache slots kept by a score-`s` eviction policy: it has
the right size, and no evicted item scores above a kept item. -/
def IsTopSet (s : ι → ℝ) (B : ℕ) (S : Finset ι) : Prop :=
  S.card = B ∧ ∀ i ∈ S, ∀ j ∉ S, s j ≤ s i

/-- The retained value of a kept set, `v` being the true (oracle) utility. -/
def retained (v : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, v i

/-- The additive hybrid eviction score `a + λ·p`
(`a` = accumulated usage, `p` = static content-probe score). -/
def hybrid (a p : ι → ℝ) (lam : ℝ) : ι → ℝ := fun i => a i + lam * p i

/-! ### The exchange kernel -/





/-! ### The oracle bound: every cheap signal family is dominated -/



/-! ### Single crossing: the structure of an additive λ-sweep -/







/-! ### z-scoring is only a reparametrisation -/




end General

/-! ### Determinism of a strictly ordered arm -/


/-! ### The calibrated NET-61 instance -/

section Calibrated

/-- Accumulated-usage signal of the calibrated four-slot instance. -/
def a4 : Fin 4 → ℝ := ![4, 3, 2, 1]

/-- Static content-probe signal: a genuinely different signal from `a4`, but
carrying the same (misleading) ordering of the slots. -/
def p4 : Fin 4 → ℝ := ![8, 6, 4, 2]

/-- True utilities, calibrated so that the hybrid retains `0.9384` (the measured
`B = 64` value) and the oracle retains `0.9954` (5.7 points higher). -/
noncomputable def v4 : Fin 4 → ℝ := ![4692 / 10000, 4692 / 10000, 4977 / 10000, 4977 / 10000]






end Calibrated

/-! ### Sharpness: the anti-alignment hypothesis cannot be dropped -/

section Sharpness

/-- Accumulated-usage signal of the two-slot sharpness instance. -/
def a2 : Fin 2 → ℝ := ![1, 0]

/-- A content probe that is *aligned* with true utility exactly where
accumulation errs. -/
def p2 : Fin 2 → ℝ := ![0, 1]

/-- True utilities of the sharpness instance. -/
def v2 : Fin 2 → ℝ := ![0, 1]




end Sharpness

/-! ### Budget, unlike probe weight, does help -/

section Budget

variable {ι : Type*} [DecidableEq ι] [Fintype ι]



end Budget

end Catalog.Combinatorics.HybridEvictionAdditiveLaw


