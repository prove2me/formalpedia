-- Prove2me | Theorems.Thm_UniversalRedundancy_savings_fraction_tendsto_zero
-- name    : UniversalRedundancy.savings_fraction_tendsto_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:41.545124+00:00
-- url     : https://prove2.me/theorems/d8f8eeda-c5de-48dc-a170-275ef30d761f
-- title:
--   The savings fraction vanishes.
-- statement:
--   **The savings fraction vanishes.**  The share of an `n`-bit message that a
--   memoryless-specialised decompressor can absorb, `log₂(n+1)/n`, tends to `0`.
--
--   ```lean
--   theorem UniversalRedundancy.savings_fraction_tendsto_zero:
--       Filter.Tendsto (fun n : ℕ => logb 2 ((n : ℝ) + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Separation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Separation.lean#L93

-- Thm stub generated from MachineLearning/UniversalRedundancy/Separation.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Separation
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

open UniversalRedundancy


variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

theorem UniversalRedundancy.savings_fraction_tendsto_zero:
    Filter.Tendsto (fun n : ℕ => logb 2 ((n : ℝ) + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by sorry
