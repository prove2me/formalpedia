-- Prove2me | Theorems.Thm_subword_complexity_le
-- name    : subword_complexity_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:10:00.010672+00:00
-- url     : https://prove2.me/theorems/27d786da-bea8-45d9-b892-c5f6c445a7d0
-- title:
--   Subword complexity le
-- statement:
--   Formal statement of `subword_complexity_le` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem subword_complexity_le{α : Type*} [Fintype α] [DecidableEq α]
--       {n k : ℕ} (hkn : k ≤ n) (s : Fin n → α) :
--       subwordComplexity hkn s ≤ Fintype.card α ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/KMerAvoidance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/KMerAvoidance.lean#L65

-- Thm stub generated from Cryptography/RamseyTheory/KMerAvoidance.lean
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

theorem subword_complexity_le{α : Type*} [Fintype α] [DecidableEq α]
    {n k : ℕ} (hkn : k ≤ n) (s : Fin n → α) :
    subwordComplexity hkn s ≤ Fintype.card α ^ k := by sorry
