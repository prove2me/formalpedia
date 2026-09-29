-- Prove2me | Theorems.Thm_Catalog_Novelty_SharedCoreServingBudget_serveCost_ratio_tendsto
-- name    : Catalog.Novelty.SharedCoreServingBudget.serveCost_ratio_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:16:56.844613+00:00
-- url     : https://prove2.me/theorems/6f95f00e-31ff-4112-a7ce-1a79aafed757
-- title:
--   Amortized model-delta law.
-- statement:
--   **Amortized model-delta law.**  As the number of served fine-tunes grows, the
--   per-model memory ratio converges to the *tail fraction* `(L - s) / L`: the shared
--   core is amortized away and only the personal tail is paid for.
--
--   ```lean
--   theorem Catalog.Novelty.SharedCoreServingBudget.serveCost_ratio_tendsto(L s : ℝ) (hL : 0 < L) :
--       Filter.Tendsto (fun n : ℕ => serveCost n L s / (n * L)) Filter.atTop
--         (nhds ((L - s) / L)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SharedCoreServingBudget.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SharedCoreServingBudget.lean#L52

-- Thm stub generated from Novelty/SharedCoreServingBudget.lean
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

theorem Catalog.Novelty.SharedCoreServingBudget.serveCost_ratio_tendsto(L s : ℝ) (hL : 0 < L) :
    Filter.Tendsto (fun n : ℕ => serveCost n L s / (n * L)) Filter.atTop
      (nhds ((L - s) / L)) := by sorry
