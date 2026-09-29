-- Prove2me | solution 1 for PRNGCompression.natToBits_inj_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:39:09.751849+00:00
-- url     : https://prove2.me/submissions/209822f9-7aff-45ca-b66d-e4eff62f26c3

-- Sol generated from MachineLearning/PRNGCompressionDepth.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionDepth
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpening the PRNG Negative Result: Families, Averages and Tightness

Second research cycle on top of `MachineLearning.PRNGCompressionBound`.  Three
natural escape routes from the pigeonhole bound are closed here, and the bound
is shown to be *tight*, which pins down exactly what a PRNG can do.

## Escape routes closed

* **"Chain several generators."**  `prng_composition_no_gain`: composing
  generators keeps the seed-length bound; the shortest seed in the chain rules.
* **"Try many generators and keep the lucky one."**  `prng_family_no_gain`:
  a family of `2 ^ m` generators with `s`-bit seeds still needs `m + s ≥ n`
  bits — selecting a generator costs exactly the bits needed to name it.
* **"Beat it on average, not in the worst case."**  `sum_length_lower` and
  `sum_KC_lower`: the *average* codeword length over all `2 ^ n` strings is at
  least `(n - k) (1 - 2 ^ (-k))` for every `k`, so no code (PRNG-based or not)
  has average length below `n - O(log n)`.

## Tightness (what a PRNG *can* do)

* `natToBits` / `exists_code_of_small_set` — any set of at most `2 ^ k` strings
  admits an injective `k`-bit code.  Combined with `prng_range_card_le` this is
  the precise statement of the positive half: PRNG outputs (a set of size
  `≤ 2 ^ s`) compress to `s` bits, and nothing else does.
* `prng_range_compresses` — the concrete corollary for the range of a PRNG.

## Application Keywords

pigeonhole tightness, average code length, generator families, seed selection
cost, Kolmogorov complexity, compression lower bounds
-/


open Finset

open PRNGCompression

/-! ## Chaining and selecting generators -/



/-! ## Average-case bounds -/



/-! ## Tightness: low-entropy sets really do compress -/








open PRNGCompression in
theorem solution{k v w : ℕ} (hv : v < 2 ^ k) (hw : w < 2 ^ k)
    (h : natToBits k v = natToBits k w) : v = w := by
  have hbit : ∀ i : Fin k, v.testBit i = w.testBit i := by
    intro i
    exact congrFun (List.ofFn_inj.mp h) i
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact hbit ⟨i, hi⟩
  · push_neg at hi
    have h1 : v < 2 ^ i := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi)
    have h2 : w < 2 ^ i := lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
