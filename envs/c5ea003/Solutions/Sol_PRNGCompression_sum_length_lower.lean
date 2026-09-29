-- Prove2me | solution 1 for PRNGCompression.sum_length_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:34:46.799283+00:00
-- url     : https://prove2.me/submissions/fa0fb292-fa0c-4984-9c25-0178adfad6c4

-- Sol generated from MachineLearning/PRNGCompressionDepth.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Theorems.Thm_PRNGCompression_card_short_le
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
theorem solution(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    (n - k) * (2 ^ n - 2 ^ (n - k)) ≤ ∑ x, (c x).length := by
  classical
  set S := univ.filter (fun x : Bits n => n - k ≤ (c x).length) with hS
  set T := univ.filter (fun x : Bits n => (c x).length ≤ n - k - 1) with hT
  have hcards : S.card + T.card = 2 ^ n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Bits n))) (p := fun x => n - k ≤ (c x).length)
    have hTeq : (univ.filter (fun x : Bits n => ¬ (n - k ≤ (c x).length))) = T := by
      apply Finset.filter_congr
      intro x _
      constructor
      · intro h1; omega
      · intro h1; omega
    rw [hTeq] at h
    simpa [hS] using h
  have hT2 : T.card ≤ 2 ^ (n - k) - 1 := by
    have hcs := card_short_le c hc (n - k - 1)
    have he : n - k - 1 + 1 = n - k := by omega
    rw [he] at hcs
    exact hcs
  have hpos : 0 < 2 ^ (n - k) := Nat.two_pow_pos _
  have hScard : 2 ^ n - 2 ^ (n - k) ≤ S.card := by omega
  have h2 : (n - k) * S.card ≤ ∑ x ∈ S, (c x).length := by
    have := Finset.card_nsmul_le_sum S (fun x => (c x).length) (n - k)
      (by intro x hx; exact (Finset.mem_filter.mp hx).2)
    simpa [mul_comm, smul_eq_mul] using this
  have h1 : ∑ x ∈ S, (c x).length ≤ ∑ x, (c x).length :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  calc (n - k) * (2 ^ n - 2 ^ (n - k)) ≤ (n - k) * S.card := Nat.mul_le_mul_left _ hScard
    _ ≤ ∑ x ∈ S, (c x).length := h2
    _ ≤ ∑ x, (c x).length := h1
