-- Prove2me | Theorems.Thm_LabelEntropy_kl_fiber_nonneg
-- name    : LabelEntropy.kl_fiber_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:55:30.073549+00:00
-- url     : https://prove2.me/theorems/7730a2e8-19e6-4ac5-8b1a-bf0a2c7a220c
-- title:
--   Key fiber estimate: comparing a sub-block `v` to a dominating block `w`.
-- statement:
--   Key fiber estimate: comparing a sub-block `v` to a dominating block `w`.
--
--   ```lean
--   theorem LabelEntropy.kl_fiber_nonneg{s : Finset ι} {v w : ι → ℝ}
--       (hv : ∀ x ∈ s, 0 ≤ v x) (hvw : ∀ x ∈ s, v x ≤ w x)
--       (hWpos : 0 < ∑ x ∈ s, w x) :
--       0 ≤ ∑ x ∈ s, v x *
--         ((Real.logb 2 (∑ y ∈ s, w y) - Real.logb 2 (w x))
--           - (Real.logb 2 (∑ y ∈ s, v y) - Real.logb 2 (v x))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/LabelEntropyDeficit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/LabelEntropyDeficit.lean#L155

-- Thm stub generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
/-
# Entropy deficit of a label coarsening

## Context (FACT round-29 #2, "THE-ORIGINAL-STANDS")

The audit of paper 99's rebuild turned on a purely information-theoretic fact:
merging distinct labels can only *destroy* label entropy, never create it, and
the amount destroyed is controlled by a nonnegative **deficit** functional.

This file develops that functional from scratch (Mathlib has no Shannon entropy
for finitely supported weight functions), in bits, with the standard convention
`0 · log 0 = 0` — which is automatic in Lean because `Real.logb 2 0 = 0`.

Main results:

* `D_eq` — closed form of the deficit `D s w = ∑ w x · (log₂ W − log₂ (w x))`;
* `D_nonneg` — the deficit of a nonnegative weight vector is `≥ 0`
  (equivalently: `nlp (∑ w) ≤ H w`, i.e. *merging a block loses entropy*);
* `kl_nonneg` — Gibbs' inequality in unnormalised form, with the zero
  convention and an explicit absolute-continuity hypothesis (which is
  **necessary**: see `kl_neg_without_absolute_continuity`);
* `D_superadditive` — concavity of entropy in deficit form: the total deficit
  of a family of weight vectors is at most the deficit of their sum.  This is
  the engine of the data-processing inequality proved in
  `Applications.JointLabelReconciliation`;
* `D_pos_of_two_positive` — a *strict* loss: whenever a merged block contains
  two strictly positive masses, entropy strictly drops.
-/

open LabelEntropy

open Finset Real

variable {ι κ : Type*}









/-! ## Gibbs' inequality (unnormalised, base 2) -/




/-! ## Concavity of entropy, in deficit form -/

theorem LabelEntropy.kl_fiber_nonneg{s : Finset ι} {v w : ι → ℝ}
    (hv : ∀ x ∈ s, 0 ≤ v x) (hvw : ∀ x ∈ s, v x ≤ w x)
    (hWpos : 0 < ∑ x ∈ s, w x) :
    0 ≤ ∑ x ∈ s, v x *
      ((Real.logb 2 (∑ y ∈ s, w y) - Real.logb 2 (w x))
        - (Real.logb 2 (∑ y ∈ s, v y) - Real.logb 2 (v x))) := by sorry
