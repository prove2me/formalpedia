-- Prove2me | solution 1 for MaxitiveMeasure.measure_eq_biSup_singletons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:13:40.473567+00:00
-- url     : https://prove2.me/submissions/6f6a479e-0b6a-432e-a60c-0eb6b5908e16

-- Sol generated from Bridges/IdempotentKMESupport.lean
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



theorem maxitive_eq (μ : MaxitiveMeasure α) (A B : Set α) :
    μ (A ∪ B) = μ A ⊔ μ B := μ.maxitive' A B



/-! ## Discrete Support -/




/-! ## Singleton Decomposition -/

/-
On a `Fintype`, the measure of a set equals the sup over its elements.
-/


/-! ## Construction from Weights -/




/-! ## Tropical KME -/




/-! ## Separating Kernel and Injectivity -/




/-! ## Support of Weight Profiles -/




/-! ## Support Identifiability -/





/-! ## Witness Characterization -/









/-! ## Topological Support -/




/-! ## Witness Separation -/




/-! ## Residuation -/




namespace MaxitiveMeasure
theorem maxitive_eq (μ : MaxitiveMeasure α) (A B : Set α) :
    μ (A ∪ B) = μ A ⊔ μ B := μ.maxitive' A B

end MaxitiveMeasure

open MaxitiveMeasure in
theorem solution[Fintype α]
    (μ : MaxitiveMeasure α) (s : Set α) :
    μ s = ⨆ x ∈ s, μ ({x} : Set α) := by
      -- Since $s$ is finite, it can be written as a finite union of singletons.
      have h_union : s = ⋃ x ∈ s, {x} := by
        aesop;
      have h_union : ∀ (t : Finset α), μ.toFun (⋃ x ∈ t, {x}) = ⨆ x ∈ t, μ.toFun {x} := by
        intro t
        induction' t using Finset.induction with x t ih;
        all_goals try exact Classical.decEq α;
        · simp +decide [ μ.empty' ];
        · convert μ.maxitive_eq { x } ( ⋃ x_1 ∈ t, { x_1 } ) using 1;
          · simp +decide [ Finset.set_biUnion_insert ];
          · simp +decide [ *, Finset.mem_insert, iSup_or, iSup_sup_eq ];
      convert h_union ( s.toFinset ) using 1;
      simp +decide [ Set.ext_iff ];
      convert rfl;
      swap;
      exacts [ Fintype.ofFinite _, by ext; simp +decide ]
