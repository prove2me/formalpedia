-- Prove2me | Definitions.Def_MachineLearning_PRNGCompressionDepth
-- name    : MachineLearning_PRNGCompressionDepth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:51:41.110061+00:00
-- url     : https://prove2.me/theorems/bbc44d27-cb1d-49ac-8845-ef53e5e86f89
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGCompressionDepth
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGCompressionDepth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGCompressionDepth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
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

namespace PRNGCompression

/-! ## Chaining and selecting generators -/



/-! ## Average-case bounds -/



/-! ## Tightness: low-entropy sets really do compress -/

/-- The `k`-bit binary expansion of `v`, as a bit string. -/
def natToBits (k v : ℕ) : List Bool := List.ofFn (fun i : Fin k => v.testBit i)






end PRNGCompression


