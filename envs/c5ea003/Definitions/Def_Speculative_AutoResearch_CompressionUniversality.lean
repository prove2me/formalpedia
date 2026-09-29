-- Prove2me | Definitions.Def_Speculative_AutoResearch_CompressionUniversality
-- name    : Speculative_AutoResearch_CompressionUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:27:25.912988+00:00
-- url     : https://prove2.me/theorems/5da42fab-c14f-4eca-ae66-cee2a1e5a0e4
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CompressionUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CompressionUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CompressionUniversality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
/-
Copyright (c) 2025. All rights reserved.

# Universal Description Systems, Derandomization, and Robustness of the
# Compression ⇋ One-Way-Function Equivalence

## Overview

This file is the second cycle of the Phase-B/M8 investigation begun in
`Shared.CompressionOneWayFunctions`.  There we proved

* the pigeonhole ceiling and its seeded (randomized) refinement, and
* the equivalence "inverting one-way functions ⇔ solving the
  compression-search (shortest-program) problem".

Here we build the missing structural layer and push the calibration further.

### 1. Self-delimiting codes and universality

`unaryTag`/`parseUnary` and `sdPair`/`parseSD` are prefix-free encodings with
verified parsing lemmas.  They yield:

* `K_univSys_le` — the **invariance theorem** in finitary form: a single
  universal decompressor simulates a whole family at an additive cost equal to
  the length of the index;
* `K_pairSys_le` — **subadditivity**: describing `x ++ y` costs at most
  `2·K x + 1 + K y`.

### 2. Derandomization: buying back randomness at the seed price

`derandomization_cost` shows that a seeded family of decompressors is simulated
by *one* deterministic decompressor at additive cost `2k + 1` for `k`-bit seeds.
Combined with `card_le_of_K_le_seeded` (which says randomness can never buy more
than `log₂|R| + 1` bits) this closes the loop: **the value of randomness for
compression is its seed length, and it is always purchasable deterministically
at that same price, up to a factor two.**

### 3. Most strings are incompressible

`density_incompressible`: for every decompressor, at most a `2^{-(c-1)}`
fraction of the strings of length `n` have complexity `≤ n - c`.

### 4. Robustness of the cryptographic equivalence

`inversion_iff_approx_compression`: the equivalence with inversion survives an
*arbitrary additive slack* `δ` in the compression task.  Finding descriptions
that are merely within `δ(n)` bits of optimal is still exactly as hard as
inverting one-way functions.  Consequently `owf_gap_universal` shows that
switching to a universal description system does not close the gap between
*existing* and *findable* descriptions.

No axioms beyond the standard three, and no `sorry`.
-/

namespace CompressionOWF

/-! ## Section 1: Self-delimiting codes -/

/-- The index `i` in unary, a separating `false`, then the program `p`. -/
def unaryTag (i : ℕ) (p : Str) : Str := List.replicate i true ++ (false :: p)

/-- Parse a unary prefix: returns the length of the leading run of `true`s and
the remainder after the separating `false`. -/
def parseUnary : Str → ℕ × Str
  | [] => (0, [])
  | false :: r => (0, r)
  | true :: r => ((parseUnary r).1 + 1, (parseUnary r).2)



/-- Self-delimiting pairing: the length of `p` in unary, then `p ++ q`. -/
def sdPair (p q : Str) : Str := unaryTag p.length (p ++ q)

/-- The matching parser for `sdPair`. -/
def parseSD (z : Str) : Str × Str :=
  ((parseUnary z).2.take (parseUnary z).1, (parseUnary z).2.drop (parseUnary z).1)



/-! ## Section 2: Universal decompressors and the invariance theorem -/

/-- The universal decompressor for a family `D` indexed by `ℕ`: the program
carries its index in unary. -/
def univSys (D : ℕ → Str → Str) : Str → Str :=
  fun z => D (parseUnary z).1 (parseUnary z).2




/-! ## Section 3: Subadditivity of complexity -/

/-- The product decompressor: split the program self-delimitingly and
concatenate the two outputs. -/
def pairSys (D₁ D₂ : Str → Str) : Str → Str :=
  fun z => D₁ (parseSD z).1 ++ D₂ (parseSD z).2


/-! ## Section 4: Derandomization at the seed price -/

/-- A decompressor family indexed by *bit strings* (seeds), packaged into a
single decompressor by self-delimiting the seed. -/
def indexSys (D : Str → Str → Str) : Str → Str :=
  fun z => D (parseSD z).1 (parseSD z).2



/-! ## Section 5: Most strings are incompressible -/


/-! ## Section 6: Robustness of the cryptographic equivalence -/

/-- An *approximate* compression-search solver: it must output a valid program
whose length is within `δ` of optimal. -/
def ApproxShortestFinder (D A : Str → Str) (δ : ℕ → ℕ) : Prop :=
  ∀ y : Str, Describable D y → D (A y) = y ∧ (A y).length ≤ K D y + δ y.length






end CompressionOWF


