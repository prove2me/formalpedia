-- Prove2me | Definitions.Def_Bridges_IdempotentKMESupport
-- name    : Bridges_IdempotentKMESupport
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:29.635778+00:00
-- url     : https://prove2.me/theorems/6a0472cc-b9b9-4c1e-bd5f-c131535af271
-- title:
--   Aether Catalog definitions — Bridges_IdempotentKMESupport
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IdempotentKMESupport`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IdempotentKMESupport.lean by skeleton subtraction
import Mathlib
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

/-- A maxitive measure on a type `α` with values in `EReal`. -/
structure MaxitiveMeasure (α : Type*) where
  toFun : Set α → EReal
  empty' : toFun ∅ = ⊥
  maxitive' : ∀ (A B : Set α), toFun (A ∪ B) = toFun A ⊔ toFun B

namespace MaxitiveMeasure

variable {α : Type*}

instance : CoeFun (MaxitiveMeasure α) (fun _ => Set α → EReal) where
  coe μ := μ.toFun





/-! ## Discrete Support -/

def suppDiscrete (μ : MaxitiveMeasure α) : Set α :=
  {x | μ {x} ≠ ⊥}



/-! ## Singleton Decomposition -/

/-
On a `Fintype`, the measure of a set equals the sup over its elements.
-/


/-! ## Construction from Weights -/

noncomputable def ofWeights [Fintype α] (w : α → EReal) : MaxitiveMeasure α where
  toFun s := ⨆ x ∈ s, w x
  empty' := by simp
  maxitive' A B := by
    show (⨆ x ∈ A ∪ B, w x) = (⨆ x ∈ A, w x) ⊔ (⨆ x ∈ B, w x)
    simp only [Set.mem_union, iSup_or, iSup_sup_eq]



/-! ## Tropical KME -/

noncomputable def tropKME_fun {α : Type*} [Fintype α]
    (k : α → α → ℝ) (w : α → EReal) : α → EReal :=
  fun y => ⨆ x, w x + (k x y : EReal)



/-! ## Separating Kernel and Injectivity -/

structure TropSeparatingKernel (α : Type*) [Fintype α] where
  k : α → α → ℝ
  reconstruct : ∀ w : α → EReal, ∀ x,
    w x = ⨅ y, (tropKME_fun k w y) - (k x y : EReal)



/-! ## Support of Weight Profiles -/

def weightSupp (w : α → EReal) : Set α := {x | w x ≠ ⊥}



/-! ## Support Identifiability -/





/-! ## Witness Characterization -/

noncomputable def singletonIndicator [DecidableEq α] (x₀ : α) : α → EReal :=
  fun y => if y = x₀ then 0 else ⊥








/-! ## Topological Support -/

def supp [TopologicalSpace α] (μ : MaxitiveMeasure α) : Set α :=
  {x | ∀ s : Set α, IsOpen s → x ∈ s → μ s ≠ ⊥}



/-! ## Witness Separation -/




/-! ## Residuation -/



end MaxitiveMeasure


