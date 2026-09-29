-- Prove2me | solution 1 for PRNGCompression.card_compressible_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:31:55.48369+00:00
-- url     : https://prove2.me/submissions/9d8f9f6c-780b-4906-90f6-c90dc2167abc

-- Sol generated from MachineLearning/PRNGCompressionCore.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Theorems.Thm_PRNGCompression_card_short_le
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counting Core for Lossless Compression: the Pigeonhole Bound

This module develops, from first principles, the counting machinery behind the
classical statement that *no lossless code can shorten all inputs*.  It is the
foundation for the negative result about pseudo-random number generators
(`MachineLearning.PRNGCompressionBound`): a PRNG is just another decompressor,
and every decompressor obeys the bounds proved here.

## Central Idea

A codeword is a finite bit string `List Bool`.  Reading a codeword as a binary
numeral *with a leading `1` prepended* gives an injection
`codeNat : List Bool → ℕ` with `2 ^ len ≤ codeNat l < 2 ^ (len + 1)`.
Hence there are fewer than `2 ^ (k+1)` codewords of length `≤ k`, and any
injective encoding of a set of size `2 ^ n` must use a codeword of length `≥ n`.

## Main Definitions

* `codeNat` — self-delimiting numeric index of a bit string
* `Bits n` — the type of `n`-bit strings, `Fin n → Bool`

## Main Results

* `codeNat_injective` — the numeric index of a bit string determines the string
* `card_short_le` — at most `2 ^ (k+1) - 1` inputs receive a codeword of length `≤ k`
* `exists_long_codeword` — pigeonhole: some `n`-bit string needs `≥ n` code bits
* `card_compressible_le` — at most a `2 ^ (1-d)` fraction of inputs can be
  compressed by `d` bits ("`d` bits of gain costs a factor `2 ^ d` of coverage")
* `card_bits` — `#(Bits n) = 2 ^ n`

## Application Keywords

lossless compression, pigeonhole bound, Kraft inequality, counting argument,
incompressibility, data compression limits
-/


open Finset

open PRNGCompression











open PRNGCompression in
theorem solution(n d : ℕ) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    2 ^ d * (univ.filter (fun x : Bits n => (c x).length + d ≤ n)).card ≤ 2 ^ (n + 1) := by
  classical
  by_cases hd : d ≤ n
  · have hsub : (univ.filter (fun x : Bits n => (c x).length + d ≤ n))
        ⊆ (univ.filter (fun x : Bits n => (c x).length ≤ n - d)) := by
      intro x hx
      have := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have h1 := Finset.card_le_card hsub
    have h2 := card_short_le c hc (n - d)
    have h3 : (2 : ℕ) ^ d * (2 ^ (n - d + 1) - 1) ≤ 2 ^ (n + 1) := by
      have hpow : (2 : ℕ) ^ d * 2 ^ (n - d + 1) = 2 ^ (n + 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc (2 : ℕ) ^ d * (2 ^ (n - d + 1) - 1) ≤ 2 ^ d * 2 ^ (n - d + 1) :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 2 ^ (n + 1) := hpow
    calc 2 ^ d * (univ.filter (fun x : Bits n => (c x).length + d ≤ n)).card
        ≤ 2 ^ d * (2 ^ (n - d + 1) - 1) := Nat.mul_le_mul_left _ (le_trans h1 h2)
      _ ≤ 2 ^ (n + 1) := h3
  · have hempty : (univ.filter (fun x : Bits n => (c x).length + d ≤ n)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _
      omega
    simp [hempty]
