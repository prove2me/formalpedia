-- Prove2me | solution 1 for UniversalRedundancy.shtarkovSum_tiedProdClass_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:36:13.661041+00:00
-- url     : https://prove2.me/submissions/ff307ebd-9c7d-4bbe-afe9-ab3ca6723222

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
theorem solution{Θ : Type*} [Nonempty Θ]
    (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) :
    (tiedProdClass S₁ S₂).shtarkovSum ≤ S₁.shtarkovSum * S₂.shtarkovSum := by
  have hpt : ∀ x : X₁ × X₂,
      (tiedProdClass S₁ S₂).maxLik x ≤ S₁.maxLik x.1 * S₂.maxLik x.2 := fun x =>
    SourceClass.maxLik_le _ fun θ =>
      mul_le_mul (S₁.le_maxLik θ x.1) (S₂.le_maxLik θ x.2) (S₂.nonneg _ _)
        (S₁.maxLik_nonneg x.1)
  calc (tiedProdClass S₁ S₂).shtarkovSum
      ≤ ∑ x : X₁ × X₂, S₁.maxLik x.1 * S₂.maxLik x.2 :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x₁ : X₁, S₁.maxLik x₁ * ∑ x₂ : X₂, S₂.maxLik x₂ := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]
    _ = S₁.shtarkovSum * S₂.shtarkovSum := by
        rw [← Finset.sum_mul]; rfl
