-- Prove2me | Theorems.Thm_UniversalRedundancy_prob_iidClass_split
-- name    : UniversalRedundancy.prob_iidClass_split
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:21.935147+00:00
-- url     : https://prove2.me/theorems/f28fa2b2-0cd5-4c87-99f7-06fb7bb32820
-- title:
--   Splitting a message of length `n₁ + n₂` into its two blocks turns the
-- statement:
--   Splitting a message of length `n₁ + n₂` into its two blocks turns the
--   memoryless class into a tied product of the two shorter memoryless classes.
--
--   ```lean
--   theorem UniversalRedundancy.prob_iidClass_split(n₁ n₂ : ℕ) (θ : Simplex A) (x : Fin (n₁ + n₂) → A) :
--       (iidClass A (n₁ + n₂)).prob θ x
--         = (tiedProdClass (iidClass A n₁) (iidClass A n₂)).prob θ
--             ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl A)).trans
--               (Equiv.sumArrowEquivProdArrow (Fin n₁) (Fin n₂) A) x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Products.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Products.lean#L193

-- Thm stub generated from MachineLearning/UniversalRedundancy/Products.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
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

open UniversalRedundancy

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*}





variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {Θ₁ Θ₂ : Type*}
  [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂]




/-! ## Tied blocks: sharing a parameter is never more expensive -/




/-! ## Consequence: the i.i.d. price is subadditive in the block length -/

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [Nonempty A] in

theorem UniversalRedundancy.prob_iidClass_split(n₁ n₂ : ℕ) (θ : Simplex A) (x : Fin (n₁ + n₂) → A) :
    (iidClass A (n₁ + n₂)).prob θ x
      = (tiedProdClass (iidClass A n₁) (iidClass A n₂)).prob θ
          ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl A)).trans
            (Equiv.sumArrowEquivProdArrow (Fin n₁) (Fin n₂) A) x) := by sorry
