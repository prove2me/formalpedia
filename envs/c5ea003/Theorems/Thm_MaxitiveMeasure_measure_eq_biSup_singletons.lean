-- Prove2me | Theorems.Thm_MaxitiveMeasure_measure_eq_biSup_singletons
-- name    : MaxitiveMeasure.measure_eq_biSup_singletons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:22.440797+00:00
-- url     : https://prove2.me/theorems/50262dc7-237e-4b09-853e-45dc0c361509
-- title:
--   Measure eq biSup singletons
-- statement:
--   Formal statement of `MaxitiveMeasure.measure_eq_biSup_singletons` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MaxitiveMeasure.measure_eq_biSup_singletons[Fintype α]
--       (μ : MaxitiveMeasure α) (s : Set α) :
--       μ s = ⨆ x ∈ s, μ ({x} : Set α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/IdempotentKMESupport.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/IdempotentKMESupport.lean#L75

-- Thm stub generated from Bridges/IdempotentKMESupport.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentKMESupport
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Support Duality and Identifiability for Idempotent Kernel Mean Embeddings

This file develops the support theory and identifiability results for tropical
(max-plus) kernel mean embeddings of maxitive measures on finite discrete spaces.

## Main results

* `MaxitiveMeasure.suppDiscrete` — discrete support definition
* `MaxitiveMeasure.measure_eq_biSup_singletons` — singleton decomposition
* `MaxitiveMeasure.ext_of_singletons` — extensionality from singletons
* `tropKME_injective_of_separating` — KME injectivity under separating kernel
* `tropKME_eq_imp_supp_eq` — KME equality implies support equality
* `identifiability_finite` — full identifiability
* `not_mem_weightSupp_iff_witness` — witness characterization of non-support
* `supp_eq_suppDiscrete` — topological = discrete support on discrete spaces

## Mathematical significance

These results establish that the tropical KME is **support-faithful** and,
under a separating kernel, **fully identifiable**. This upgrades the tropical
KME pipeline from representation theory to inverse theory.
-/


open scoped BigOperators

/-! ## Maxitive Measures on Finite Types -/


open MaxitiveMeasure

variable {α : Type*}






/-! ## Discrete Support -/




/-! ## Singleton Decomposition -/

/-
On a `Fintype`, the measure of a set equals the sup over its elements.
-/

theorem MaxitiveMeasure.measure_eq_biSup_singletons[Fintype α]
    (μ : MaxitiveMeasure α) (s : Set α) :
    μ s = ⨆ x ∈ s, μ ({x} : Set α) := by sorry
