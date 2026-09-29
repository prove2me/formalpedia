-- Prove2me | Theorems.Thm_LabelEntropy_D_superadditive
-- name    : LabelEntropy.D_superadditive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:55:28.165532+00:00
-- url     : https://prove2.me/theorems/1acaa4be-cd92-4743-b60e-8d4a04f0e4c7
-- title:
--   Concavity of entropy (deficit form).
-- statement:
--   **Concavity of entropy (deficit form).**  Splitting a nonnegative weight
--   vector into a family of pieces cannot increase the total deficit.
--
--   ```lean
--   theorem LabelEntropy.D_superadditive{s : Finset ι} {t : Finset κ} {v : κ → ι → ℝ}
--       (hv : ∀ y ∈ t, ∀ x ∈ s, 0 ≤ v y x) :
--       ∑ y ∈ t, D s (v y) ≤ D s (fun x => ∑ y ∈ t, v y x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/LabelEntropyDeficit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/LabelEntropyDeficit.lean#L199

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

theorem LabelEntropy.D_superadditive{s : Finset ι} {t : Finset κ} {v : κ → ι → ℝ}
    (hv : ∀ y ∈ t, ∀ x ∈ s, 0 ≤ v y x) :
    ∑ y ∈ t, D s (v y) ≤ D s (fun x => ∑ y ∈ t, v y x) := by sorry
