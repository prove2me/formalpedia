-- Prove2me | Theorems.Thm_EOSWidth_eosVec_inDigitSpan_iff
-- name    : EOSWidth.eosVec_inDigitSpan_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:34:44.71753+00:00
-- url     : https://prove2.me/theorems/db15b66c-19e6-4038-bce5-2526ca192cf6
-- title:
--   Width controls distinctness only through the digit block.
-- statement:
--   **Width controls distinctness only through the digit block.**  A zero-padded
--   EOS of width `E` is a tropical combination of the digit atoms — hence invisible
--   to every max-plus readout as a category of its own — exactly when `E ≤ D`.
--
--   ```lean
--   theorem EOSWidth.eosVec_inDigitSpan_iff{N D E : ℕ} (hDN : D < N) :
--       InDigitSpan N D (eosVec N E) ↔ E ≤ D := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean#L275

-- Thm stub generated from Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean
import Mathlib
import Definitions.Def_Tropical_NeuralNetworks_EOSWidthTropicalSeparation

/-!
# Tropical separation theory of boundary tokens ("EOS width")

This file gives a max-plus (tropical) model of the empirical phenomenon
recorded in round NET-26 (*EOS-WIDTH-DISTRIBUTION-SHIFT*): a boundary
("end-of-sequence") input of width `E` cures a recurrent carry-wall failure
robustly exactly when it owns dimensions that no digit token uses, and is
seed-fragile when its width sits inside the digit subspace (`E ≤ D`).

The formal claim isolated here is that the *control variable is
representational distinctness, not width*:

* `eos_mem_digitSpan_iff` — a boundary vector lies in the tropical (max-plus)
  span of the one-hot digit atoms **iff** it has no exclusive dimension.
* `score_supported_eq_tropComb_of_digitScores` — if it has no exclusive
  dimension, then for **every** max-plus readout `w` the boundary response is a
  fixed tropical combination of the digit responses: the readout cannot tell the
  boundary from a digit step except through digit-controlled quantities.
* `margin_le_of_no_exclusive_dim` — consequently the boundary-vs-digit margin is
  bounded by the boundary's own coefficients, uniformly in `w`.
* `exclusive_dim_unbounded_margin` — with one exclusive dimension the margin
  becomes unbounded (indeed the digit responses can be driven to the tropical
  zero `⊥`), and
* `exclusive_dim_margin_robust` — the separation survives arbitrary bounded
  perturbations of the readout weights.

Everything is stated over the max-plus semiring on `WithBot ℝ`
(`⊕ = max = ⊔`, `⊙ = +`, tropical zero `⊥ = -∞`, tropical one `0`).
-/

open EOSWidth

open Finset








/-! ## Part 1: which boundary vectors are tropically indistinguishable -/







/-! ## Part 2: max-plus readouts cannot separate a span member -/





/-! ## Part 3: an exclusive dimension buys unbounded, robust separation -/







/-! ## Part 4: zero-padded EOS embeddings -/

theorem EOSWidth.eosVec_inDigitSpan_iff{N D E : ℕ} (hDN : D < N) :
    InDigitSpan N D (eosVec N E) ↔ E ≤ D := by sorry
