-- Prove2me | solution 1 for PRNGCompression.card_short_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:30:23.067729+00:00
-- url     : https://prove2.me/submissions/33241c13-b784-4e54-9d79-66c5640b3b7c

-- Sol generated from MachineLearning/PRNGCompressionCore.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Theorems.Thm_PRNGCompression_codeNat_injective
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




lemma one_le_codeNat (l : List Bool) : 1 ≤ codeNat l := by
  induction l with
  | nil => simp [codeNat]
  | cons b t ih => simp [codeNat]; omega

/-- A bit string of length `k` gets an index `< 2 ^ (k+1)`. -/
lemma codeNat_lt (l : List Bool) : codeNat l < 2 ^ (l.length + 1) := by
  induction l with
  | nil => simp [codeNat]
  | cons b t ih =>
      have hb : codeNat (b :: t) ≤ 2 * codeNat t + 1 := by
        simp [codeNat]; split <;> omega
      have h2 : (2 : ℕ) ^ (t.length + 1 + 1) = 2 * 2 ^ (t.length + 1) := by ring
      simp only [List.length_cons]
      omega






open PRNGCompression in
theorem solution{X : Type*} [Fintype X] [DecidableEq X]
    (c : X → List Bool) (hc : Function.Injective c) (k : ℕ) :
    (univ.filter (fun x => (c x).length ≤ k)).card ≤ 2 ^ (k + 1) - 1 := by
  classical
  have key : (univ.filter (fun x => (c x).length ≤ k)).card
      ≤ (Finset.Icc 1 (2 ^ (k + 1) - 1)).card := by
    apply Finset.card_le_card_of_injOn (fun x => codeNat (c x))
    · intro x hx
      have hx2 : (c x).length ≤ k := (Finset.mem_filter.mp hx).2
      have h1 := one_le_codeNat (c x)
      have h2 := codeNat_lt (c x)
      have h3 : (2 : ℕ) ^ ((c x).length + 1) ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro a _ b _ h
      exact hc (codeNat_injective h)
  simpa using key
