-- Prove2me | solution 1 for PRNGCompression.exists_code_of_small_set
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:41:35.455193+00:00
-- url     : https://prove2.me/submissions/cc1cd7b9-f397-4409-a908-6191ccc2b436

-- Sol generated from MachineLearning/PRNGCompressionDepth.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Theorems.Thm_PRNGCompression_natToBits_inj_of_lt
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


@[simp] lemma natToBits_length (k v : ℕ) : (natToBits k v).length = k := by
  simp [natToBits]






open PRNGCompression in
theorem solution(n k : ℕ) (A : Finset (Bits n)) (hA : A.card ≤ 2 ^ k) :
    ∃ c : Bits n → List Bool, (∀ x ∈ A, (c x).length = k) ∧ Set.InjOn c A := by
  classical
  let e := A.equivFin
  refine ⟨fun x => if h : x ∈ A then natToBits k (e ⟨x, h⟩ : Fin A.card) else [], ?_, ?_⟩
  · intro x hx
    simp only [dif_pos hx, natToBits_length]
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have hvx : ((e ⟨x, hx⟩ : Fin A.card) : ℕ) < 2 ^ k := lt_of_lt_of_le (e ⟨x, hx⟩).isLt hA
    have hvy : ((e ⟨y, hy⟩ : Fin A.card) : ℕ) < 2 ^ k := lt_of_lt_of_le (e ⟨y, hy⟩).isLt hA
    have hnum := natToBits_inj_of_lt hvx hvy hxy
    exact congrArg Subtype.val (e.injective (Fin.ext hnum))
