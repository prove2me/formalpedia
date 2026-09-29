-- Prove2me | solution 1 for subword_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:20:24.789321+00:00
-- url     : https://prove2.me/submissions/e1aeacf6-e950-4db7-b510-4941b8bdbd6d

-- Sol generated from Cryptography/RamseyTheory/KMerAvoidance.lean
import Mathlib
import Definitions.Def_Cryptography_RamseyTheory_KMerAvoidance
/-
# K-Mer Avoidance: Combinatorial Framework

A rigorous combinatorial framework for k-mer avoidance in sequences over finite alphabets.

## Main Results

1. **Ramsey Threshold** (`kmer_repeat_threshold`): Any sequence of length ≥ α^k + k over
   an alphabet of size α must contain a repeated k-mer.

2. **Subword Complexity Bound** (`subword_complexity_le`): The number of distinct k-mers
   in any sequence is at most α^k.

3. **Avoidance Capacity** (`exists_kmer_repeat_free`): There exist sequences of length
   α^k + k - 1 with no repeated k-mers (sharpness of the threshold).

4. **Composition Bias Detection** (`biased_seq_reduced_complexity`): Sequences with
   restricted symbol usage have strictly fewer distinct k-mers.
-/

open Finset Fintype Function

/-! ## Core Definitions -/





/-! ## The Ramsey Threshold Theorem

The key insight: the map `i ↦ kmer s k i` sends `Fin (n - k + 1)` into `Fin k → α`.
When `n - k + 1 > |α|^k`, the pigeonhole principle forces a collision.
-/

/-
**Ramsey Threshold**: If `n ≥ |α|^k + k`, then every sequence `s : Fin n → α`
    contains a repeated k-mer. This is the fundamental pigeonhole bound.
-/

/-
**Subword Complexity Bound**: The number of distinct k-mers is at most |α|^k.
-/

/-! ## Sharpness: Existence of Long Repeat-Free Sequences

We show the threshold `α^k + k` is tight by constructing sequences of length
`α^k + k - 1` that avoid k-mer repeats. The construction uses an injective
enumeration of all `α^k` possible k-mers. -/


/-! ## Composition Bias and Reduced Complexity

Sequences that use fewer symbols have exponentially fewer possible k-mers.
This connects to cryptographic applications: biased key material has
detectable statistical signatures through k-mer analysis. -/

/-
**Bias Detection**: If a sequence uses at most `b` distinct symbols where `b < |α|`,
    then its subword complexity is bounded by `b^k` rather than `|α|^k`.
-/

/-! ## Structural Properties of K-Mers -/

/-
**Overlap Lemma**: Two consecutive k-mers share k-1 symbols. This is the
    key structural property enabling sliding-window analysis.
-/

/-
K-mers of length 1 are just individual symbols.
-/

/-! ## K-Mer Entropy and Cryptographic Applications

The k-mer framework has direct cryptographic relevance: randomness testing
of key material, bias detection in PRNGs, and bounds on distinguisher advantage. -/



/-
**Soundness of K-Mer Distinguisher**: A biased sequence with fewer than |α| symbols
    has strictly fewer than |α|^k distinct k-mers (for k ≥ 1).
-/

/-! ## Threshold Tightness and Subthreshold Existence -/

/-
**Subthreshold Existence**: Below the Ramsey threshold, repeat-free sequences
    can exist. Specifically, if `n - k + 1 ≤ |α|^k`, then the pigeonhole argument
    does not force a collision — an injective k-mer map is not ruled out by cardinality.
-/

/-
**Constant Sequence Complexity**: A constant sequence has subword complexity exactly 1
    (when n ≥ k and k ≥ 1), the minimum possible for a nonempty sequence.
-/

/-
**DNA Alphabet Complexity**: The 4-letter DNA alphabet {A,C,G,T} can produce
    at most 4^k distinct k-mers. This is a direct corollary of the general bound.
-/

/-
**Repetition Threshold for DNA**: Over the 4-letter DNA alphabet, the Ramsey
    threshold specializes: for any n and k with n ≥ 4^k + k, every DNA sequence
    of length n must contain a repeated k-mer.
-/

theorem solution{α : Type*} [Fintype α] [DecidableEq α]
    {n k : ℕ} (hkn : k ≤ n) (s : Fin n → α) :
    subwordComplexity hkn s ≤ Fintype.card α ^ k := by
  convert Finset.card_le_univ ( Finset.image ( fun i : Fin ( n - k + 1 ) => fun j : Fin k => s ⟨ i.val + j.val, by omega ⟩ ) Finset.univ );
  simp +decide
