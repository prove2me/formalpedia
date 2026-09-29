-- Prove2me | Theorems.Thm_UniversalRedundancy_markov_redundancy_bits_le
-- name    : UniversalRedundancy.markov_redundancy_bits_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:03.824688+00:00
-- url     : https://prove2.me/theorems/43f41d6c-c05e-4b82-a59a-9de34f5c567e
-- title:
--   The price of universality for Markov sources, in bits.
-- statement:
--   **The price of universality for Markov sources, in bits.**  One universal
--   code is within `log₂ #A + #A² · log₂ (n+1) + 1` bits of the code tailored to the
--   true chain, uniformly over chains and messages.
--
--   ```lean
--   theorem UniversalRedundancy.markov_redundancy_bits_le[Nonempty A] (n : ℕ) (θ : MarkovParam A)
--       (x : Fin (n + 1) → A) (hx : 0 < (markovClass A n).prob θ x) :
--       ((markovClass A n).nmlCodeLength x : ℝ)
--         ≤ logb 2 (1 / (markovClass A n).prob θ x)
--           + (logb 2 (Fintype.card A)
--               + (Fintype.card A : ℝ) * (Fintype.card A : ℝ) * logb 2 ((n : ℝ) + 1)) + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Markov.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Markov.lean#L159

-- Thm stub generated from MachineLearning/UniversalRedundancy/Markov.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Markov
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality III: first-order Markov sources

Third instalment of the thread (after `UniversalRedundancy.Core` and
`UniversalRedundancy.Types`).  Memoryless sources were shown to cost at most
`#A · log₂ (n+1)` bits of universality.  Here we build the class of first-order
Markov chains — the standard model of *sources with memory* — from scratch,
including the (non-trivial) proof that the chain measure is a probability
measure on `Aⁿ⁺¹`, and bound its price of universality.

## Central Idea

The likelihood of a Markov chain factors as

`p_θ(x) = ν(x₀) · ∏_{j<n} T(x_j, x_{j+1})`,

so it depends on `x` only through the first symbol and the matrix of *transition
counts*.  That is a statistic with at most `#A · (n+1)^(#A·#A)` values, and the
abstract counting theorem `shtarkovSum_le_of_product_form` converts this
directly into the redundancy bound

`Cₛ ≤ #A · (n+1)^(#A²)`,  i.e.  `price ≤ log₂ #A + #A² · log₂ (n+1)` bits.

## Main Results

* `markovChain_sum_one` — the Markov chain measure on `Aⁿ⁺¹` is normalized
  (proved by induction on `n`, propagating the initial law through the kernel)
* `markovClass` — the source class of first-order Markov chains
* `shtarkovSum_markovClass_le` — `Cₛ ≤ #A · (n+1)^(#A · #A)`
* `markov_redundancy_bits_le` — bit form: one universal code is within
  `log₂ #A + #A² · log₂ (n+1) + 1` bits of the code tuned to the true chain,
  simultaneously for every chain and every message

## Application Keywords

Markov source, transition counts, universal coding with memory, Rissanen
redundancy, sufficient statistic
-/


open Finset Real

open UniversalRedundancy

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem UniversalRedundancy.markov_redundancy_bits_le[Nonempty A] (n : ℕ) (θ : MarkovParam A)
    (x : Fin (n + 1) → A) (hx : 0 < (markovClass A n).prob θ x) :
    ((markovClass A n).nmlCodeLength x : ℝ)
      ≤ logb 2 (1 / (markovClass A n).prob θ x)
        + (logb 2 (Fintype.card A)
            + (Fintype.card A : ℝ) * (Fintype.card A : ℝ) * logb 2 ((n : ℝ) + 1)) + 1 := by sorry
