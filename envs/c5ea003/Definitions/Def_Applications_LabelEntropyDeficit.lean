-- Prove2me | Definitions.Def_Applications_LabelEntropyDeficit
-- name    : Applications_LabelEntropyDeficit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:07.456548+00:00
-- url     : https://prove2.me/theorems/0a7a1fc0-06ee-487c-b330-4f2c83e64065
-- title:
--   Aether Catalog definitions — Applications_LabelEntropyDeficit
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LabelEntropyDeficit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LabelEntropyDeficit.lean by skeleton subtraction
import Mathlib
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

namespace LabelEntropy

open Finset Real

variable {ι κ : Type*}

/-- Pointwise Shannon term in bits, `nlp t = -t·log₂ t`, with `nlp 0 = 0`. -/
noncomputable def nlp (t : ℝ) : ℝ := -(t * Real.logb 2 t)


/-- Shannon entropy (bits) of a nonnegative weight function on a finite set. -/
noncomputable def H (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, nlp (w i)

/-- Entropy **deficit**: how much entropy is lost by collapsing the whole block
`s` into a single label of mass `∑ w`. -/
noncomputable def D (s : Finset ι) (w : ι → ℝ) : ℝ := H s w - nlp (∑ i ∈ s, w i)





/-! ## Gibbs' inequality (unnormalised, base 2) -/




/-! ## Concavity of entropy, in deficit form -/



/-! ## Strict loss -/


end LabelEntropy


