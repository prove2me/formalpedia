-- Prove2me | Definitions.Def_Speculative_AutoResearch_CompressionLasVegasDecision
-- name    : Speculative_AutoResearch_CompressionLasVegasDecision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:28:27.31636+00:00
-- url     : https://prove2.me/theorems/d5ca7414-3b8e-4663-9240-9224ec7cb834
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CompressionLasVegasDecision
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CompressionLasVegasDecision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CompressionLasVegasDecision.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
/-
Copyright (c) 2025. All rights reserved.

# Las Vegas *decision* oracles for compressibility and the one-way boundary

## Overview

`Catalog/Novelty/CompressionLasVegasOWF.lean` showed that a one-way function
defeats every Las Vegas *search* algorithm (finitely many seeds) totally: some
value in the range is missed by all seeds at once.  Compression search, however,
is only one of the tasks in the compression ⇋ cryptography dictionary.  The
*decision* task — "does `y` have a `D`-program of length `n` extending the prefix
`w`?" — carries no verifiable certificate, so at first sight randomizing it might
be cheaper.

This file shows it is not.  The chain is:

1. `decisionToFinder_correct_at` : the bit-by-bit reconstruction of
   `Speculative.AutoResearch.CompressionSearchToDecision` needs the decision
   oracle to be correct **only at the one string being compressed** (proved by
   globalizing a locally correct oracle with a classical one, `globalize`);
2. `las_vegas_decider_inverts` : if, for every value in the range of `f`, *some*
   seed of a finite list carries a locally correct oracle, then a deterministic
   algorithm inverts `f` — the reconstruction produces a program, and the program
   is verifiable even though the oracle's answers are not;
3. `owf_defeats_las_vegas_decider` : consequently, under a one-way function there
   is a describable `y` at which **every** seeded decision oracle is wrong.
   Randomized *decision* of compressibility is blocked exactly like randomized
   search.

Finally `canonical_decision_finder` records that the obstruction is purely
computational: the classical (noncomputable) oracle is correct and does solve
compression search, so nothing information-theoretic stands in the way.

All results are proved from scratch; there are no axioms and no `sorry`.
-/

namespace CompressionLasVegasDecision

open CompressionOWF CompressionLasVegas
open scoped Classical

/-! ## Section 1: local correctness suffices for reconstruction -/

/-- A decision oracle is *locally correct at `y`* if it answers the prefix
compressibility questions about `y` correctly (its answers about other strings
are unconstrained). -/
def LocallyCorrectAt (D : Str → Str) (dec : Str → Str → ℕ → Bool) (y : Str) : Prop :=
  ∀ w n, dec y w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y

/-- Replace the answers of `dec` about strings other than `y₀` by the (classical)
correct answers.  This is a purely mathematical device: it turns a locally
correct oracle into a globally correct one without touching the queries that the
reconstruction at `y₀` actually makes. -/
noncomputable def globalize (D : Str → Str) (dec : Str → Str → ℕ → Bool) (y₀ : Str) :
    Str → Str → ℕ → Bool :=
  fun y w n => if y = y₀ then dec y w n else decide (∃ p : Str, p.length = n ∧ D (w ++ p) = y)




/-! ## Section 2: Las Vegas decision oracles still invert -/

/-- The deterministic algorithm assembled from a seeded family of decision
oracles: reconstruct a program from each seed's oracle, then keep the first
reconstruction that verifies. -/
noncomputable def decisionTryList (f : Str → Str) (dec : Str → Str → Str → ℕ → Bool)
    (fuel : ℕ → ℕ) (R : List Str) : Str → Str :=
  tryList f (fun r => decisionToFinder (dec r) fuel) R




/-! ## Section 3: the obstruction is computational, not informational -/

/-- The classical (noncomputable) decision oracle for `D`. -/
noncomputable def canonicalDec (D : Str → Str) : Str → Str → ℕ → Bool :=
  fun y w n => decide (∃ p : Str, p.length = n ∧ D (w ++ p) = y)




end CompressionLasVegasDecision


