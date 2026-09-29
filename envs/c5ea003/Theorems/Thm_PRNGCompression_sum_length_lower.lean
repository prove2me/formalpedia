-- Prove2me | Theorems.Thm_PRNGCompression_sum_length_lower
-- name    : PRNGCompression.sum_length_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:45:31.609158+00:00
-- url     : https://prove2.me/theorems/e10b1427-f64c-4c66-baef-1d7d32cb6342
-- title:
--   Average length bound.
-- statement:
--   **Average length bound.**  For every injective code and every `k < n`, the
--   total codeword length over all `2 ^ n` strings is at least
--   `(n - k) (2 ^ n - 2 ^ (n - k))`; dividing by `2 ^ n`, the average length is at
--   least `(n - k)(1 - 2 ^ (-k))`.  Taking `k ≈ log₂ n` gives average `≥ n - O(log n)`:
--   compression cannot even win *on average* against uniform data.
--
--   ```lean
--   theorem PRNGCompression.sum_length_lower(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
--       (hc : Function.Injective c) :
--       (n - k) * (2 ^ n - 2 ^ (n - k)) ≤ ∑ x, (c x).length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionDepth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionDepth.lean#L69

-- Thm stub generated from MachineLearning/PRNGCompressionDepth.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
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

theorem PRNGCompression.sum_length_lower(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    (n - k) * (2 ^ n - 2 ^ (n - k)) ≤ ∑ x, (c x).length := by sorry
