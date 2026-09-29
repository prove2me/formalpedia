-- Prove2me | solution 1 for UniversalRedundancy.redundancy_rate_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:28:02.341805+00:00
-- url     : https://prove2.me/submissions/81038d31-6158-49ca-a547-cbe305a8a5aa

-- Sol generated from MachineLearning/UniversalRedundancy/Types.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality II: parametric classes pay only `O(log n)`

Continuation of `MachineLearning.UniversalRedundancy.Core`.  There the minimax
redundancy of a source class was identified *exactly* with `log₂ Cₛ`, the log of
the Shtarkov sum.  Here we bound `Cₛ` for the classes that matter in practice —
memoryless (i.i.d.) sources and Markov sources — and obtain closed-form bounds
in the message length `n` and the *class complexity*.

## Central Idea

The abstract engine is a **sufficient statistic** bound: if the likelihood
`p_θ x` depends on `x` only through a statistic `T x` taking `N` values, then

`Cₛ ≤ N`.

Indeed the fibre of `T` over a value `s` has some cardinality `k`, on which the
maximum likelihood is a constant `M`; since `k · p_θ x ≤ 1` for every `θ`, also
`k · M ≤ 1`, so each fibre contributes at most `1` to `∑ₓ maxₜ p_θ x`.

For a class whose likelihood is a product of `m` factors drawn from a finite
"feature alphabet" `B` (times a factor depending on a finite initial statistic
in `C`), the counts of the features form such a statistic, giving

`Cₛ ≤ #C · (m+1) ^ #B`.

Specialising: memoryless sources over an alphabet `A` on messages of length `n`
give `Cₛ ≤ (n+1) ^ #A`, and first-order Markov sources give
`Cₛ ≤ #A · (n+1) ^ (#A · #A)`.  In bits: the price of universality is at most
`#A · log₂ (n+1)` resp. `log₂ #A + #A² · log₂ (n+1)` bits — logarithmic in `n`,
matching the Rissanen-style `(d/2) log₂ n` rate up to the constant factor `2`
in front of the parameter dimension `d`.

## Main Results

* `SourceClass.shtarkovSum_le_card_statistic` — sufficient-statistic bound
* `SourceClass.shtarkovSum_le_of_product_form` — counting bound for product
  likelihoods, `Cₛ ≤ #C · (m+1) ^ #B`
* `iidClass`, `shtarkovSum_iidClass_le` — memoryless sources: `Cₛ ≤ (n+1) ^ #A`
* `markovClass`, `shtarkovSum_markovClass_le` — Markov sources:
  `Cₛ ≤ #A · (n+1) ^ (#A * #A)`
* `iid_redundancy_bits_le`, `markov_redundancy_bits_le` — the bit-level
  statements: a single universal code is within `#A log₂(n+1) + 1` bits of the
  code tailored to the true memoryless source, for *every* source and *every*
  message
* `iid_redundancy_rate_tendsto_zero` — the per-symbol price of universality
  tends to `0`: specialisation buys a vanishing fraction of the message

## Application Keywords

method of types, sufficient statistic, Rissanen redundancy, Markov sources,
universal coding, parametric class complexity
-/


open Finset Real

open UniversalRedundancy

/-! ## Sufficient-statistic bound on the Shtarkov sum -/

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)


/-! ## Counting statistic for product likelihoods -/




open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)



/-! ## Memoryless (i.i.d.) sources -/



variable {A : Type*} [Fintype A] [DecidableEq A]







open UniversalRedundancy in
theorem solution(c : ℝ) :
    Filter.Tendsto (fun n : ℕ => (c * logb 2 ((n : ℝ) + 1) + 1) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => logb 2 x ^ 1 / (1 * x + (-1)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_pow_logb_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hshift : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hcomp : Filter.Tendsto
      (fun n : ℕ => logb 2 ((n : ℝ) + 1) ^ 1 / (1 * ((n : ℝ) + 1) + (-1)))
      Filter.atTop (nhds 0) := hbase.comp hshift
  have hlog : Filter.Tendsto (fun n : ℕ => logb 2 ((n : ℝ) + 1) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    refine hcomp.congr fun n => ?_
    simp only [pow_one, one_mul]
    ring_nf
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have := ((hlog.const_mul c).add hinv)
  rw [mul_zero, add_zero] at this
  refine this.congr fun n => ?_
  field_simp
