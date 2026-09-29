-- Prove2me | solution 1 for UniversalRedundancy.maxLik_markovClass_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:08.202623+00:00
-- url     : https://prove2.me/submissions/16541c53-e332-44b1-9dae-bfcf6dc8dc36

-- Sol generated from MachineLearning/UniversalRedundancy/Markov.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Markov
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
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









open UniversalRedundancy in
theorem solution[Nonempty A] (n : ℕ) (x : Fin (n + 1) → A) :
    0 < (markovClass A n).maxLik x := by
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  set θ : MarkovParam A :=
    ⟨(fun _ => (Fintype.card A : ℝ)⁻¹, fun _ _ => (Fintype.card A : ℝ)⁻¹),
      ⟨⟨fun _ => by positivity, by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp⟩,
        fun _ => ⟨fun _ => by positivity, by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp⟩⟩⟩ with hθ
  have hp : 0 < (markovClass A n).prob θ x := by
    simp only [markovClass, hθ]
    exact mul_pos (by positivity) (Finset.prod_pos fun j _ => by positivity)
  exact lt_of_lt_of_le hp ((markovClass A n).le_maxLik θ x)
