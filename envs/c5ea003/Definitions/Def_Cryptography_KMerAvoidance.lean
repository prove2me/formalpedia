-- Prove2me | Definitions.Def_Cryptography_KMerAvoidance
-- name    : Cryptography_KMerAvoidance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:18:30.664745+00:00
-- url     : https://prove2.me/theorems/b515f07f-d08f-4e3c-9c4c-354966f72be7
-- title:
--   Aether Catalog definitions — Cryptography_KMerAvoidance
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.KMerAvoidance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/KMerAvoidance.lean by skeleton subtraction
import Mathlib
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

/-- A `KMer` of a sequence `s : Fin n → α` starting at position `i` with window size `k`
    is the restriction of `s` to positions `i, i+1, ..., i+k-1`.
    Requires `k ≤ n` to ensure valid indexing. -/
def kmer {α : Type*} {n k : ℕ} (hkn : k ≤ n) (s : Fin n → α) (i : Fin (n - k + 1)) :
    Fin k → α :=
  fun j => s ⟨i.val + j.val, by omega⟩

/-- A sequence is `KMerRepeatFree` if all k-mers at distinct positions are distinct. -/
def KMerRepeatFree {α : Type*} {n k : ℕ} (hkn : k ≤ n) (s : Fin n → α) : Prop :=
  Function.Injective (kmer hkn s)

/-- The subword complexity at window size `k` counts the number of distinct k-mers. -/
noncomputable def subwordComplexity {α : Type*} {n k : ℕ} [DecidableEq α]
    (hkn : k ≤ n) (s : Fin n → α) : ℕ :=
  (Finset.univ.image (kmer hkn s)).card

/-- A sequence has `CompositionBias` if it uses at most `b` distinct symbols (b < |α|). -/
def CompositionBias {α : Type*} {n : ℕ} [DecidableEq α]
    (s : Fin n → α) (b : ℕ) : Prop :=
  (Finset.univ.image s).card ≤ b

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


