-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Products
-- name    : MachineLearning_UniversalRedundancy_Products
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:04:21.985985+00:00
-- url     : https://prove2.me/theorems/17ddcc80-36fb-47f4-8cfb-4b10ab3c2f79
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Products
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Products`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Products.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
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

namespace UniversalRedundancy

namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*}



end SourceClass

/-- The product of two source classes: two independent blocks whose parameters
are chosen independently. -/
noncomputable def prodClass {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]
    {Θ₁ Θ₂ : Type*} (S₁ : SourceClass X₁ Θ₁) (S₂ : SourceClass X₂ Θ₂) :
    SourceClass (X₁ × X₂) (Θ₁ × Θ₂) where
  prob θ x := S₁.prob θ.1 x.1 * S₂.prob θ.2 x.2
  nonneg θ x := mul_nonneg (S₁.nonneg _ _) (S₂.nonneg _ _)
  sum_one θ := by
    rw [Fintype.sum_prod_type]
    calc ∑ x₁ : X₁, ∑ x₂ : X₂, S₁.prob θ.1 x₁ * S₂.prob θ.2 x₂
        = ∑ x₁ : X₁, S₁.prob θ.1 x₁ * ∑ x₂ : X₂, S₂.prob θ.2 x₂ :=
          Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]
      _ = ∑ x₁ : X₁, S₁.prob θ.1 x₁ := by rw [S₂.sum_one]; simp
      _ = 1 := S₁.sum_one _

variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ₁ Θ₂ : Type*}
  [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂]




/-! ## Tied blocks: sharing a parameter is never more expensive -/


/-- Two blocks driven by *one shared* parameter. -/
noncomputable def tiedProdClass {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]
    {Θ : Type*} (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) :
    SourceClass (X₁ × X₂) Θ where
  prob θ x := S₁.prob θ x.1 * S₂.prob θ x.2
  nonneg θ x := mul_nonneg (S₁.nonneg _ _) (S₂.nonneg _ _)
  sum_one θ := by
    rw [Fintype.sum_prod_type]
    calc ∑ x₁ : X₁, ∑ x₂ : X₂, S₁.prob θ x₁ * S₂.prob θ x₂
        = ∑ x₁ : X₁, S₁.prob θ x₁ * ∑ x₂ : X₂, S₂.prob θ x₂ :=
          Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]
      _ = ∑ x₁ : X₁, S₁.prob θ x₁ := by rw [S₂.sum_one]; simp
      _ = 1 := S₁.sum_one _


/-! ## Consequence: the i.i.d. price is subadditive in the block length -/

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]




end UniversalRedundancy


