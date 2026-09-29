-- Prove2me | solution 1 for PRNGCompression.exists_long_codeword
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:37:02.626358+00:00
-- url     : https://prove2.me/submissions/04fc75e8-f395-4fd5-8fa7-d18f375fddeb

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
theorem solution(n : ℕ) (c : Bits n → List Bool)
    (hc : Function.Injective c) : ∃ x, n ≤ (c x).length := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨fun i => i.elim0, Nat.zero_le _⟩
  by_contra h
  push_neg at h
  have hfull : (univ.filter (fun x : Bits n => (c x).length ≤ n - 1)) = univ := by
    apply Finset.filter_true_of_mem
    intro x _
    have := h x; omega
  have hcard := card_short_le c hc (n - 1)
  rw [hfull] at hcard
  have hu : (univ : Finset (Bits n)).card = 2 ^ n := by simp [Bits]
  have h2 : n - 1 + 1 = n := by omega
  rw [hu, h2] at hcard
  have : 0 < 2 ^ n := Nat.two_pow_pos n
  omega
