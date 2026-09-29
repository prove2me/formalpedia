-- Prove2me | solution 1 for Catalog.Novelty.SharedCoreServingBudget.shared_core_agreement_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:31.090985+00:00
-- url     : https://prove2.me/submissions/b8d8618d-64f0-465f-9946-74f0eeac935a

-- Sol generated from Novelty/SharedCoreServingBudget.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_SharedCoreServingBudget
import Theorems.Thm_Catalog_Novelty_KVDecisionDissociation_strictTop_of_margin

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
theorem solution{L n : ℕ} (u v : Fin L → Fin n → ℝ)
    (i : Fin L → Fin n) (S : Finset (Fin L)) (eps : ℝ)
    (hmargin : ∀ l ∈ S, ∀ j, j ≠ i l → 2 * eps < u l (i l) - u l j)
    (hclose : ∀ l ∈ S, ∀ j, |u l j - v l j| ≤ eps) :
    S ⊆ agreeSet u v i ∧ S.card ≤ (agreeSet u v i).card := by
  have hsub : S ⊆ agreeSet u v i := by
    intro l hl
    have hbase : IsStrictTop (u l) (i l) := by
      intro j hj
      have h0 : (0 : ℝ) ≤ eps := le_trans (abs_nonneg _) (hclose l hl j)
      have := hmargin l hl j hj
      linarith
    have hfine : IsStrictTop (v l) (i l) :=
      strictTop_of_margin (u l) (v l) (i l) eps (hmargin l hl) (hclose l hl)
    simpa [agreeSet] using ⟨hbase, hfine⟩
  exact ⟨hsub, Finset.card_le_card hsub⟩
