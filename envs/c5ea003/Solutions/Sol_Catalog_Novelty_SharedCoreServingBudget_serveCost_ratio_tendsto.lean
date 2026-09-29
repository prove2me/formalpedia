-- Prove2me | solution 1 for Catalog.Novelty.SharedCoreServingBudget.serveCost_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:30.267908+00:00
-- url     : https://prove2.me/submissions/a0248e0b-4ee7-4a66-b540-ebaa77dcd85c

-- Sol generated from Novelty/SharedCoreServingBudget.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_SharedCoreServingBudget

/-!
# Shared-core / personal-tail serving: the amortized model-delta law (NET-51, Part C)

NET-51's practical claim is: *a multi-fine-tune server can share about 22 of 24
layers of KV machinery at ≥ 0.92 top-1 decision agreement, while the tail must be
per-model.*  This file proves the two halves of that claim.

* **Budget.**  `serveCost n L s = s + n * (L - s)` is the memory of serving `n`
  fine-tunes that share `s` of `L` layers.  `serveCost_eq_saving` exhibits the
  saving `(n-1) * s` over independent serving, and `serveCost_ratio_tendsto`
  shows the amortized ratio converges to the *tail fraction* `(L - s)/L`
  — with `L = 24`, `s = 22` this is `1/12` (`serveCost_ratio_tail_24_22`).

* **Safety.**  `shared_core_agreement_bound` proves that whenever the shared
  layers carry a top-1 margin exceeding twice the sharing error, *every* shared
  layer reproduces the base model's attention decision, so the fraction of layers
  with provably identical decisions is at least `|S| / L`; `agreement_24_22` is
  the numerical instance of the measured configuration: certifying `22` of the
  `24` layers gives a provable-agreement fraction of at least `11/12 ≈ 0.9167`.

* **Boundary.**  `cosine_certificate_is_void` records that no cosine threshold can
  replace the margin hypothesis: sharing justified by cosine alone may flip
  decisions.  This is exactly why the measured tail (cosine `0.983`, agreement
  `0.568`) is not shareable.
-/

open Catalog.Novelty.SharedCoreServingBudget

open Finset Catalog.Novelty.KVDecisionDissociation

/-! ### 1. The amortized budget -/






/-! ### 2. Decision-agreement guarantee for the shared core -/






open Catalog.Novelty.SharedCoreServingBudget in
theorem solution(L s : ℝ) (hL : 0 < L) :
    Filter.Tendsto (fun n : ℕ => serveCost n L s / (n * L)) Filter.atTop
      (nhds ((L - s) / L)) := by
  have h0 : Filter.Tendsto (fun n : ℕ => (s / L) / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (s / L)
  have h1 : Filter.Tendsto (fun n : ℕ => (s / L) / n + (L - s) / L) Filter.atTop
      (nhds (0 + (L - s) / L)) := h0.add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hL' : L ≠ 0 := ne_of_gt hL
  simp only [serveCost]
  field_simp
