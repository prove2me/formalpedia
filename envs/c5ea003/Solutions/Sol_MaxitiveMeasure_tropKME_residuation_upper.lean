-- Prove2me | solution 1 for MaxitiveMeasure.tropKME_residuation_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:08:32.615743+00:00
-- url     : https://prove2.me/submissions/ef1cfd4e-98ca-4891-9670-f1de54732004

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






/-! ## Discrete Support -/




/-! ## Singleton Decomposition -/

/-
On a `Fintype`, the measure of a set equals the sup over its elements.
-/


/-! ## Construction from Weights -/




/-! ## Tropical KME -/


theorem le_tropKME_fun {α : Type*} [Fintype α]
    (k : α → α → ℝ) (w : α → EReal) (x y : α) :
    w x + (k x y : EReal) ≤ tropKME_fun k w y :=
  le_iSup (fun x => w x + (k x y : EReal)) x


/-! ## Separating Kernel and Injectivity -/




/-! ## Support of Weight Profiles -/




/-! ## Support Identifiability -/





/-! ## Witness Characterization -/









/-! ## Topological Support -/




/-! ## Witness Separation -/




/-! ## Residuation -/




open MaxitiveMeasure in
theorem solution{α : Type*} [Fintype α]
    (k : α → α → ℝ) (w : α → EReal) (x : α) :
    w x ≤ ⨅ y, tropKME_fun k w y - (k x y : EReal) := by
      refine' le_iInf fun y => _;
      by_contra h_contra;
      cases h : w x <;> cases h' : tropKME_fun k w y <;> simp_all +decide [ sub_eq_add_neg ];
      · unfold tropKME_fun at h';
        aesop;
      · norm_cast at *;
        rename_i a b;
        have := le_tropKME_fun k w x y;
        rw [ h, h' ] at this ; norm_cast at this ; linarith;
      · exact absurd h' ( ne_of_gt ( lt_of_lt_of_le ( by simp +decide [ h ] ) ( le_tropKME_fun k w x y ) ) );
      · unfold tropKME_fun at h';
        exact absurd ( h' ▸ le_ciSup ( Finite.bddAbove_range fun x => w x + ( k x y : EReal ) ) x ) ( by simp +decide [ h ] )
