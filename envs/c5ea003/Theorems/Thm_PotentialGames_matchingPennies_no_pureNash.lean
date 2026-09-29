-- Prove2me | Theorems.Thm_PotentialGames_matchingPennies_no_pureNash
-- name    : PotentialGames.matchingPennies_no_pureNash
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:49:54.645126+00:00
-- url     : https://prove2.me/theorems/9dc81891-c958-4d61-af1a-31231b592a0b
-- title:
--   Matching Pennies has no pure-strategy Nash equilibrium.
-- statement:
--   **Matching Pennies has no pure-strategy Nash equilibrium.**
--   Proved directly by case analysis on the two moves: in each of the four cases the
--   loser of the round can strictly improve by switching moves.  This proof is
--   self-contained and does not depend on `matchingPennies_no_exactPotential`.
--
--   ```lean
--   theorem PotentialGames.matchingPennies_no_pureNash:
--       ¬ ∃ p : Profile MPStrategy, IsPureNash matchingPenniesPayoff p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/PotentialGames.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/PotentialGames.lean#L98

-- Thm stub generated from Speculative/NumberTheory/PotentialGames.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_PotentialGames
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Potential games and the Matching Pennies boundary example

This file develops a minimal framework for finite strategic games, exact
potential functions, and pure-strategy Nash equilibria.  The main positive
result, `exists_pureNash_of_exactPotential`, states that any finite game which
admits an exact potential function has a pure-strategy Nash equilibrium (a
maximizer of the potential).

As a boundary example we formalize *Matching Pennies*, the classic 2×2 zero-sum
game with no pure-strategy equilibrium.  We prove directly, by case analysis,
that it has no pure Nash equilibrium (`matchingPennies_no_pureNash`), and deduce
from the general theorem that it therefore admits no exact potential function
(`matchingPennies_no_exactPotential`).
-/

open PotentialGames

open Function






/-! ## Matching Pennies -/






instance : Nonempty (Profile MPStrategy) := ⟨fun _ => MPMove.heads⟩

theorem PotentialGames.matchingPennies_no_pureNash:
    ¬ ∃ p : Profile MPStrategy, IsPureNash matchingPenniesPayoff p := by sorry
