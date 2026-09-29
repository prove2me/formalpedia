-- Prove2me | solution 1 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.net61_calibrated_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:42:13.117128+00:00
-- url     : https://prove2.me/submissions/34f19751-b8be-46be-a5c1-ab996602ffef

-- Sol generated from Combinatorics/HybridEvictionAdditiveLaw.lean
import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
import Theorems.Thm_Catalog_Combinatorics_HybridEvictionAdditiveLaw_sum_le_sum_of_sdiff_dominated
import Theorems.Thm_Catalog_Combinatorics_HybridEvictionAdditiveLaw_topSet_eq_initial_of_strictAnti

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

open Catalog.Combinatorics.HybridEvictionAdditiveLaw

open Finset


variable {ι : Type*} [DecidableEq ι]




/-! ### The exchange kernel -/





/-! ### The oracle bound: every cheap signal family is dominated -/

/-- **Oracle optimality.**  A set kept by scoring with the true utility `v`
retains at least as much as any other set of the same size. -/
theorem oracle_max (v : ι → ℝ) {B : ℕ} {O T : Finset ι} (hO : IsTopSet v B O)
    (hT : T.card = B) : retained v T ≤ retained v O := by
  refine sum_le_sum_of_sdiff_dominated v (by rw [hT, hO.1]) ?_
  intro j hj i hi
  rw [Finset.mem_sdiff] at hj hi
  exact hO.2 i hi.1 j hj.2


/-! ### Single crossing: the structure of an additive λ-sweep -/







/-! ### z-scoring is only a reparametrisation -/





/-! ### Determinism of a strictly ordered arm -/


/-! ### The calibrated NET-61 instance -/





private theorem hybrid4_strictAnti {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ i j : Fin 4, i < j → hybrid a4 p4 lam j < hybrid a4 p4 lam i := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hybrid, a4, p4, Fin.lt_def] <;> linarith

/-- The kept set of every nonnegative-λ arm of the calibrated instance at
budget `2` is forced to be `{0, 1}`. -/
theorem net61_hybrid_kept_set {lam : ℝ} (hlam : 0 ≤ lam) {S : Finset (Fin 4)}
    (hS : IsTopSet (hybrid a4 p4 lam) 2 S) : S = {0, 1} := by
  have := topSet_eq_initial_of_strictAnti (by norm_num) _ (hybrid4_strictAnti hlam) hS
  rw [this]
  decide

/-- The oracle keeps `{2, 3}` on the calibrated instance. -/
theorem net61_oracle_kept_set : IsTopSet v4 2 {2, 3} := by
  refine ⟨by decide, ?_⟩
  intro i hi j hj
  fin_cases i <;> fin_cases j <;> simp_all [v4] <;> norm_num




/-! ### Sharpness: the anti-alignment hypothesis cannot be dropped -/









/-! ### Budget, unlike probe weight, does help -/


variable {ι : Type*} [DecidableEq ι] [Fintype ι]





open Catalog.Combinatorics.HybridEvictionAdditiveLaw in
theorem solution{lam : ℝ} (hlam : 0 ≤ lam) {S O : Finset (Fin 4)}
    (hS : IsTopSet (hybrid a4 p4 lam) 2 S) (hO : IsTopSet v4 2 O) :
    retained v4 S = 9384 / 10000 ∧ retained v4 O = 9954 / 10000 ∧
      retained v4 O - retained v4 S = 570 / 10000 := by
  have hSeq : S = {0, 1} := net61_hybrid_kept_set hlam hS
  have hval : retained v4 S = 9384 / 10000 := by
    rw [hSeq]; simp [retained, v4, Finset.sum_insert]; norm_num
  have hOval : retained v4 O = 9954 / 10000 := by
    have h1 : retained v4 O ≤ retained v4 ({2, 3} : Finset (Fin 4)) :=
      oracle_max v4 net61_oracle_kept_set hO.1
    have h2 : retained v4 ({2, 3} : Finset (Fin 4)) ≤ retained v4 O :=
      oracle_max v4 hO (by decide)
    have h3 : retained v4 ({2, 3} : Finset (Fin 4)) = 9954 / 10000 := by
      simp [retained, v4]; norm_num
    linarith
  refine ⟨hval, hOval, by rw [hval, hOval]; norm_num⟩
