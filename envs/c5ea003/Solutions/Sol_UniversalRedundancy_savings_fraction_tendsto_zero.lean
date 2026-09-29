-- Prove2me | solution 1 for UniversalRedundancy.savings_fraction_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:29:47.310801+00:00
-- url     : https://prove2.me/submissions/0ef5403d-c006-4f21-9180-bf63e63fa97c

-- Sol generated from MachineLearning/UniversalRedundancy/Separation.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Separation
import Theorems.Thm_UniversalRedundancy_redundancy_rate_tendsto_zero
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







open UniversalRedundancy in
theorem solution:
    Filter.Tendsto (fun n : ℕ => logb 2 ((n : ℝ) + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
  have h := redundancy_rate_tendsto_zero 1
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsub := h.sub hinv
  rw [sub_zero] at hsub
  refine hsub.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hpos
    field_simp
    ring
