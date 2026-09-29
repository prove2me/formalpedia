-- Prove2me | Theorems.Thm_LabelEntropy_gibbs_term
-- name    : LabelEntropy.gibbs_term
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:55:12.344037+00:00
-- url     : https://prove2.me/theorems/1fb8ee53-c81b-4d38-a839-309116ae82ea
-- title:
--   Per-term Gibbs bound: `(a - b)/log 2 ≤ a·(log₂ a - log₂ b)` for nonnegative
-- statement:
--   Per-term Gibbs bound: `(a - b)/log 2 ≤ a·(log₂ a - log₂ b)` for nonnegative
--   `a, b` with `b = 0 → a = 0`.
--
--   ```lean
--   theorem LabelEntropy.gibbs_term{a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : b = 0 → a = 0) :
--       (a - b) / Real.log 2 ≤ a * (Real.logb 2 a - Real.logb 2 b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/LabelEntropyDeficit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/LabelEntropyDeficit.lean#L83

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

theorem LabelEntropy.gibbs_term{a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : b = 0 → a = 0) :
    (a - b) / Real.log 2 ≤ a * (Real.logb 2 a - Real.logb 2 b) := by sorry
