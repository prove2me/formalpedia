-- Prove2me | solution 1 for UniversalRedundancy.markov_redundancy_bits_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:27:52.714622+00:00
-- url     : https://prove2.me/submissions/055f579a-dc6c-4e45-8a8f-22583452a58b

-- Sol generated from MachineLearning/UniversalRedundancy/Markov.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Markov
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_nmlCodeLength_le
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_le_of_product_form
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_pos
import Theorems.Thm_UniversalRedundancy_maxLik_markovClass_pos
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





/-- **Markov sources: `Cₛ ≤ #A · (n+1)^(#A · #A)`.**  The price of universality
over the whole first-order Markov class is at most
`log₂ #A + #A² · log₂ (n+1)` bits — still only logarithmic in the message
length, with the class complexity `#A²` entering as a multiplier. -/
theorem shtarkovSum_markovClass_le [Nonempty A] (n : ℕ) :
    (markovClass A n).shtarkovSum
      ≤ (Fintype.card A : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (Fintype.card A * Fintype.card A) := by
  classical
  have h := (markovClass A n).shtarkovSum_le_of_product_form
    (B := A × A) (C := A) (m := n)
    (feat := fun x j => (x j.castSucc, x j.succ)) (init := fun x => x 0)
    (g := fun θ ab => θ.1.2 ab.1 ab.2) (h := fun θ a => θ.1.1 a)
    (by intro θ x; rfl)
  rwa [Fintype.card_prod] at h




open UniversalRedundancy in
theorem solution[Nonempty A] (n : ℕ) (θ : MarkovParam A)
    (x : Fin (n + 1) → A) (hx : 0 < (markovClass A n).prob θ x) :
    ((markovClass A n).nmlCodeLength x : ℝ)
      ≤ logb 2 (1 / (markovClass A n).prob θ x)
        + (logb 2 (Fintype.card A)
            + (Fintype.card A : ℝ) * (Fintype.card A : ℝ) * logb 2 ((n : ℝ) + 1)) + 1 := by
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have h1 := (markovClass A n).nmlCodeLength_le (maxLik_markovClass_pos n) hx
  have hC := shtarkovSum_markovClass_le (A := A) n
  have hbase : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hbase] at hC
  have hle : logb 2 (markovClass A n).shtarkovSum
      ≤ logb 2 ((Fintype.card A : ℝ) * ((n : ℝ) + 1) ^ (Fintype.card A * Fintype.card A)) :=
    Real.logb_le_logb_of_le (by norm_num) (markovClass A n).shtarkovSum_pos hC
  rw [Real.logb_mul (ne_of_gt hcard) (by positivity), Real.logb_pow] at hle
  push_cast at hle
  linarith
