-- Prove2me | solution 1 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.topSet_eq_initial_of_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:11:33.214768+00:00
-- url     : https://prove2.me/submissions/ae95e1c2-dd35-43fc-bbbc-bb3a9e8f0708

-- Sol generated from Combinatorics/HybridEvictionAdditiveLaw.lean
import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw

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

/-- Two equicardinal sets have equicardinal symmetric-difference halves. -/
theorem card_sdiff_eq_card_sdiff {S T : Finset ι} (h : T.card = S.card) :
    (T \ S).card = (S \ T).card := by
  have h1 := Finset.card_sdiff_add_card_inter T S
  have h2 := Finset.card_sdiff_add_card_inter S T
  have h3 : (T ∩ S).card = (S ∩ T).card := by rw [Finset.inter_comm]
  omega




/-! ### The oracle bound: every cheap signal family is dominated -/



/-! ### Single crossing: the structure of an additive λ-sweep -/







/-! ### z-scoring is only a reparametrisation -/





/-! ### Determinism of a strictly ordered arm -/


/-! ### The calibrated NET-61 instance -/











/-! ### Sharpness: the anti-alignment hypothesis cannot be dropped -/









/-! ### Budget, unlike probe weight, does help -/


variable {ι : Type*} [DecidableEq ι] [Fintype ι]





open Catalog.Combinatorics.HybridEvictionAdditiveLaw in
theorem solution{n B : ℕ} (hB : B ≤ n) (s : Fin n → ℝ)
    (hs : ∀ i j : Fin n, i < j → s j < s i) {S : Finset (Fin n)} (hS : IsTopSet s B S) :
    S = (Finset.univ.filter (fun i : Fin n => (i : ℕ) < B)) := by
  set L : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < B) with hL
  have hcardL : L.card = B := by
    have : L.card = (Finset.range B).card := by
      apply Finset.card_bij (fun (i : Fin n) _ => (i : ℕ))
      · intro a ha; simp [hL] at ha ⊢; exact ha
      · intro a _ b _ hab; exact Fin.val_injective hab
      · intro b hb
        simp only [Finset.mem_range] at hb
        exact ⟨⟨b, lt_of_lt_of_le hb hB⟩, by simp [hL, hb], rfl⟩
    simpa using this
  have hsub : L ⊆ S := by
    by_contra hcon
    obtain ⟨i, hiL, hiS⟩ := Finset.not_subset.1 hcon
    have hLS : (L \ S).Nonempty := ⟨i, Finset.mem_sdiff.2 ⟨hiL, hiS⟩⟩
    have hcard : S.card = L.card := by rw [hS.1, hcardL]
    have hSL : (S \ L).Nonempty := Finset.card_pos.1 (by
      rw [card_sdiff_eq_card_sdiff hcard]
      exact Finset.card_pos.2 hLS)
    obtain ⟨j, hj⟩ := hSL
    rw [Finset.mem_sdiff] at hj
    have hjB : B ≤ (j : ℕ) := by
      by_contra hlt
      exact hj.2 (by simp [hL]; omega)
    have hiB : (i : ℕ) < B := by simpa [hL] using hiL
    have hij : i < j := by
      have : (i : ℕ) < (j : ℕ) := lt_of_lt_of_le hiB hjB
      exact this
    have h1 : s j < s i := hs i j hij
    have h2 : s i ≤ s j := hS.2 j hj.1 i hiS
    linarith
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS.1, hcardL])).symm
