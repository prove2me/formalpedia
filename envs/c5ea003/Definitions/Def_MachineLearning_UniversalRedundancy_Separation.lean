-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Separation
-- name    : MachineLearning_UniversalRedundancy_Separation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:20:44.781231+00:00
-- url     : https://prove2.me/theorems/35decff8-8778-4acf-b8af-bcef6176d8ad
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Separation
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Separation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Separation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality VI: parametric versus unrestricted classes

Final instalment: the answer to the research question of Phase A / Question 1,
*is a specialised decompressor worth pursuing?*

## Central Idea

Two extreme classes on the same message space `Bits n = Fin n → Bool` of
`n`-bit files:

* the **memoryless class** (one unknown bias): the price of universality is
  sandwiched between `½ log₂ n − 2` and `log₂ (n+1)` bits
  (`bernoulli_price_sandwich`);
* the **deterministic class** `{δ_y}` — one source per file, the richest
  possible class, i.e. "a decompressor specialised to each individual file":
  here the price is exactly `n` bits (`price_deltaClass_bits`).

So the transfer of bits from the message into a shared decompressor is governed
entirely by the *complexity of the class*, not by the length of the data: a
`d`-parameter class moves `Θ(log n)` bits, while a class rich enough to name
every file moves nothing at all — the `n` bits that a specialised decompressor
saves on its own file are exactly the `n` bits the universal scheme must spend
to say which decompressor was used.

## Main Results

* `deltaClass` — the class of deterministic (point-mass) sources
* `shtarkovSum_deltaClass` — `Cₛ = #X` exactly
* `price_deltaClass_bits` — on `n`-bit files the price is exactly `n` bits
* `price_separation` — the separation: on the same message space, the
  memoryless class costs `≤ log₂ (n+1)` bits while the unrestricted
  deterministic class costs exactly `n` bits
* `savings_fraction_tendsto_zero` — the fraction of the message that a
  memoryless-specialised decompressor can absorb tends to `0`

## Application Keywords

class complexity, universal coding, specialised decompressor, pigeonhole bound,
minimax redundancy separation
-/


open Finset Real

namespace UniversalRedundancy

/-- The class of deterministic sources: one point mass per message. -/
noncomputable def deltaClass (X : Type*) [Fintype X] [DecidableEq X] :
    SourceClass X X where
  prob θ x := if x = θ then 1 else 0
  nonneg θ x := by split <;> norm_num
  sum_one θ := by simp

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]






end UniversalRedundancy


