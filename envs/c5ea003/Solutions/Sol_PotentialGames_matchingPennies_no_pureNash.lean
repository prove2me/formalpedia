-- Prove2me | solution 1 for PotentialGames.matchingPennies_no_pureNash
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:51.8031+00:00
-- url     : https://prove2.me/submissions/9b174aae-9586-451d-a278-192d22059ed3

-- Sol generated from Speculative/NumberTheory/PotentialGames.lean
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





open PotentialGames in
theorem solution:
    ¬ ∃ p : Profile MPStrategy, IsPureNash matchingPenniesPayoff p := by
  rintro ⟨p, hp⟩
  -- Case split on both players' moves; the losing player can profitably deviate.
  rcases hpr : p MPPlayer.row with _ | _ <;> rcases hpc : p MPPlayer.col with _ | _
  · -- (heads, heads): Column deviates to tails to break the match.
    have h := hp MPPlayer.col MPMove.tails
    simp only [matchingPenniesPayoff, deviate, hpr, hpc, Function.update_self,
      Function.update_of_ne (by decide : MPPlayer.row ≠ MPPlayer.col), reduceCtorEq,
      if_true, if_false] at h
    norm_num at h
  · -- (heads, tails): Row deviates to tails to create a match.
    have h := hp MPPlayer.row MPMove.tails
    simp only [matchingPenniesPayoff, deviate, hpr, hpc, Function.update_self,
      Function.update_of_ne (by decide : MPPlayer.col ≠ MPPlayer.row), reduceCtorEq,
      if_true, if_false] at h
    norm_num at h
  · -- (tails, heads): Row deviates to heads to create a match.
    have h := hp MPPlayer.row MPMove.heads
    simp only [matchingPenniesPayoff, deviate, hpr, hpc, Function.update_self,
      Function.update_of_ne (by decide : MPPlayer.col ≠ MPPlayer.row), reduceCtorEq,
      if_true, if_false] at h
    norm_num at h
  · -- (tails, tails): Column deviates to heads to break the match.
    have h := hp MPPlayer.col MPMove.heads
    simp only [matchingPenniesPayoff, deviate, hpr, hpc, Function.update_self,
      Function.update_of_ne (by decide : MPPlayer.row ≠ MPPlayer.col), reduceCtorEq,
      if_true, if_false] at h
    norm_num at h
