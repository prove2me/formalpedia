-- Prove2me | solution 1 for UniversalRedundancy.maxLik_prodClass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:27:58.430707+00:00
-- url     : https://prove2.me/submissions/f502404e-5287-41dd-9994-bff1624d1815

-- Sol generated from MachineLearning/UniversalRedundancy/Products.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_le
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_nonneg
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality VII: structural laws (calibration, monotonicity,
# multiplicativity)

Second research cycle on the thread.  Having computed the price of universality
for concrete classes, we isolate the *structural laws* the price obeys, which
explain the numbers of Parts II–VI and give a calculus for new classes.

## Central Idea

Three laws for the Shtarkov sum `Cₛ`:

* **Calibration.**  A class with a single source has `Cₛ = 1`: the price of
  universality is exactly `0` bits, so the theory is not measuring an artefact.
* **Monotonicity.**  Enlarging the class can only increase `Cₛ`; a reindexing
  (in particular a subclass) never costs more.  Price is a monotone functional
  of class complexity.
* **Multiplicativity.**  For a product class — two independent blocks with
  *independently chosen* parameters — `Cₛ = Cₛ¹ · Cₛ²`, i.e. the price in bits
  is *additive* across independent blocks.

Additivity is the structural reason why an unrestricted per-symbol class costs
`Θ(n)` bits (Part VI) while a class with a single shared parameter costs only
`Θ(log n)` (Parts II and V): sharing a parameter across blocks, rather than
re-choosing it, is exactly what turns a linear price into a logarithmic one.

## Main Results

* `shtarkovSum_of_subsingleton` — `Cₛ = 1` for a one-source class
* `shtarkovSum_reindex_le` — monotonicity under reindexing/subclasses
* `prodClass`, `shtarkovSum_prodClass` — `Cₛ = Cₛ¹ · Cₛ²` for product classes
* `price_prodClass_add` — the price in bits is additive over independent blocks
* `shtarkovSum_le_of_relabel` — transport of the price along relabellings
* `tiedProdClass`, `shtarkovSum_tiedProdClass_le` — with a *shared* parameter
  the price is only *sub*additive: sharing is what buys the savings
* `shtarkovSum_iidClass_submultiplicative`, `iid_price_subadditive` —
  `Cₛ(n₁+n₂) ≤ Cₛ(n₁)·Cₛ(n₂)` for the memoryless class

## Application Keywords

universal coding, Shtarkov sum, product source class, additivity of redundancy,
class complexity
-/


open Finset Real

open UniversalRedundancy

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*}





variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ₁ Θ₂ : Type*}
  [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂]




/-! ## Tied blocks: sharing a parameter is never more expensive -/




/-! ## Consequence: the i.i.d. price is subadditive in the block length -/

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]





open UniversalRedundancy in
theorem solution(S₁ : SourceClass X₁ Θ₁) (S₂ : SourceClass X₂ Θ₂)
    (x : X₁ × X₂) :
    (prodClass S₁ S₂).maxLik x = S₁.maxLik x.1 * S₂.maxLik x.2 := by
  refine le_antisymm ?_ ?_
  · refine SourceClass.maxLik_le _ fun θ => ?_
    exact mul_le_mul (S₁.le_maxLik θ.1 x.1) (S₂.le_maxLik θ.2 x.2) (S₂.nonneg _ _)
      (S₁.maxLik_nonneg x.1)
  · obtain ⟨θ₁, hθ₁⟩ := Finite.exists_max fun θ : Θ₁ => S₁.prob θ x.1
    obtain ⟨θ₂, hθ₂⟩ := Finite.exists_max fun θ : Θ₂ => S₂.prob θ x.2
    have h₁ : S₁.maxLik x.1 = S₁.prob θ₁ x.1 :=
      le_antisymm (S₁.maxLik_le fun θ => hθ₁ θ) (S₁.le_maxLik θ₁ x.1)
    have h₂ : S₂.maxLik x.2 = S₂.prob θ₂ x.2 :=
      le_antisymm (S₂.maxLik_le fun θ => hθ₂ θ) (S₂.le_maxLik θ₂ x.2)
    rw [h₁, h₂]
    exact (prodClass S₁ S₂).le_maxLik (θ₁, θ₂) x
