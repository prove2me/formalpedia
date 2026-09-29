-- Prove2me | Theorems.Thm_CompressionOWF_rebuild_correct
-- name    : CompressionOWF.rebuild_correct
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:39:12.314731+00:00
-- url     : https://prove2.me/theorems/bb7b02c5-c0e0-45a7-8c3e-a520b7413479
-- title:
--   Correctness of the reconstruction.
-- statement:
--   **Correctness of the reconstruction.**  If some length-`n` continuation of
--   `w` is a `D`-program for `y`, then `rebuild` outputs one, of exactly the right
--   length.
--
--   ```lean
--   theorem CompressionOWF.rebuild_correct(D : Str → Str) (y : Str) (dec : Str → ℕ → Bool)
--       (hdec : ∀ w n, dec w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y) :
--       ∀ (n : ℕ) (w : Str), (∃ p : Str, p.length = n ∧ D (w ++ p) = y) →
--         D (rebuild dec n w) = y ∧ (rebuild dec n w).length = w.length + n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/CompressionSearchToDecision.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/CompressionSearchToDecision.lean#L53

-- Thm stub generated from Speculative/AutoResearch/CompressionSearchToDecision.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
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

open CompressionOWF

/-! ## Section 1: Bit-by-bit reconstruction from a decision oracle -/

theorem CompressionOWF.rebuild_correct(D : Str → Str) (y : Str) (dec : Str → ℕ → Bool)
    (hdec : ∀ w n, dec w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y) :
    ∀ (n : ℕ) (w : Str), (∃ p : Str, p.length = n ∧ D (w ++ p) = y) →
      D (rebuild dec n w) = y ∧ (rebuild dec n w).length = w.length + n := by sorry
