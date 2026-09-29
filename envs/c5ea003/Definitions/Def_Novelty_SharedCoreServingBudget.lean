-- Prove2me | Definitions.Def_Novelty_SharedCoreServingBudget
-- name    : Novelty_SharedCoreServingBudget
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:27.920265+00:00
-- url     : https://prove2.me/theorems/7019dd6d-2123-428a-b39b-b413dbe8e41e
-- title:
--   Aether Catalog definitions — Novelty_SharedCoreServingBudget
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SharedCoreServingBudget`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SharedCoreServingBudget.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation

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

namespace Catalog.Novelty.SharedCoreServingBudget

open Finset Catalog.Novelty.KVDecisionDissociation

/-! ### 1. The amortized budget -/

/-- Memory cost of serving `n` fine-tunes of an `L`-layer model when the first
`s` layers of KV machinery are shared and the remaining `L - s` are per-model. -/
def serveCost (n : ℕ) (L s : ℝ) : ℝ := s + n * (L - s)





/-! ### 2. Decision-agreement guarantee for the shared core -/

open Classical in
/-- The set of layers on which the two models provably make the *same* top-1
attention decision `i l`. -/
noncomputable def agreeSet {L n : ℕ} (u v : Fin L → Fin n → ℝ) (i : Fin L → Fin n) :
    Finset (Fin L) :=
  Finset.univ.filter fun l => IsStrictTop (u l) (i l) ∧ IsStrictTop (v l) (i l)




end Catalog.Novelty.SharedCoreServingBudget


