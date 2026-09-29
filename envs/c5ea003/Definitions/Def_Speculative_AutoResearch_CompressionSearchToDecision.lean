-- Prove2me | Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
-- name    : Speculative_AutoResearch_CompressionSearchToDecision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:27:52.572468+00:00
-- url     : https://prove2.me/theorems/2bdd4688-3277-41a3-8a23-64950d3ba47f
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CompressionSearchToDecision
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CompressionSearchToDecision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CompressionSearchToDecision.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
/-
Copyright (c) 2025. All rights reserved.

# Search-to-Decision for Compression, and its Cryptographic Payoff

## Overview

Third cycle of the Phase-B/M8 investigation (`Shared.CompressionOneWayFunctions`,
`Shared.CompressionUniversality`).

The previous cycles compared two *search* tasks — inverting a function and
finding shortest programs — and proved them equivalent.  The literature on
polynomial-time Kolmogorov complexity phrases hardness assumptions instead in
terms of the *decision* problem "is `K(y) ≤ n`?" (MINKT), so a complete
characterization must bridge search and decision.  That bridge is the classical
bit-by-bit prefix reconstruction, which we formalize here:

* `rebuild` — reconstruct a program one bit at a time from a *decision* oracle
  for the conditional predicate "some length-`n` continuation of the prefix `w`
  is a program for `y`";
* `rebuild_correct` — the reconstruction returns a genuine program of exactly the
  promised length (proved by induction on the number of remaining bits);
* `decisionToFinder_correct` — combining the reconstruction with the bounded
  search of `leastFrom` turns the decision oracle into a *shortest*-program
  finder;
* `decision_solves_inversion` — hence into an inverter;
* `owf_no_prefix_decider` — **cryptographic payoff**: if `f` is one-way for a
  class, then no algorithm of the class can decide the prefix-compressibility
  predicate of `f`.  The decision version of compression is hard exactly when
  one-way functions exist.

Together with cycle 1 (search version) and cycle 2 (approximate version), this
gives the promised map: *validity, exact-shortest, approximate-shortest and
prefix-decision compression tasks all sit at the same cryptographic level.*

No axioms beyond the standard three, no `sorry`.
-/

namespace CompressionOWF

/-! ## Section 1: Bit-by-bit reconstruction from a decision oracle -/

/-- Reconstruct a program bit by bit.  `dec w n` is meant to answer
"is there a string `p` of length `n` with `D (w ++ p) = y`?".  Starting from the
empty prefix and the correct total length, `rebuild` walks down the binary tree
of prefixes, always taking a branch that keeps a solution alive. -/
def rebuild (dec : Str → ℕ → Bool) : ℕ → Str → Str
  | 0, w => w
  | n + 1, w =>
      if dec (w ++ [false]) n then rebuild dec n (w ++ [false])
      else rebuild dec n (w ++ [true])


/-! ## Section 2: From the decision oracle to a shortest-program finder -/

/-- The compressor built from a decision oracle: first find the optimal length by
bounded search, then reconstruct the program bit by bit. -/
def decisionToFinder (dec : Str → Str → ℕ → Bool) (fuel : ℕ → ℕ) : Str → Str :=
  fun y => rebuild (dec y) (leastFrom (fun n => dec y [] n) (fuel y.length)) []



/-! ## Section 3: Cryptographic payoff -/



end CompressionOWF


