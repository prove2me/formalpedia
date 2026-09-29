-- Prove2me | Definitions.Def_Speculative_NumberTheory_PotentialGames
-- name    : Speculative_NumberTheory_PotentialGames
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:15.845009+00:00
-- url     : https://prove2.me/theorems/feaf2057-5368-4079-b8b8-26784806b910
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_PotentialGames
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.PotentialGames`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/PotentialGames.lean by skeleton subtraction
import Mathlib
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

namespace PotentialGames

open Function

/-- A (pure-strategy) profile assigns to each player `i` a strategy in `S i`. -/
def Profile {ι : Type*} (S : ι → Type*) : Type _ := ∀ i, S i

/-- The profile obtained from `p` by having player `i` unilaterally switch to
strategy `s`, leaving everyone else unchanged. -/
def deviate {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (p : Profile S) (i : ι) (s : S i) : Profile S :=
  Function.update p i s

/-- A profile `p` is a pure-strategy Nash equilibrium for the payoff family
`payoff` if no player can strictly improve their own payoff by deviating. -/
def IsPureNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (payoff : ι → Profile S → ℝ) (p : Profile S) : Prop :=
  ∀ (i : ι) (s : S i), payoff i (deviate p i s) ≤ payoff i p

/-- `Φ` is an exact potential function for `payoff` if every unilateral
deviation changes the deviating player's payoff by exactly the same amount as it
changes `Φ`. -/
def IsExactPotential {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (payoff : ι → Profile S → ℝ) (Φ : Profile S → ℝ) : Prop :=
  ∀ (i : ι) (p : Profile S) (s : S i),
    payoff i (deviate p i s) - payoff i p = Φ (deviate p i s) - Φ p


/-! ## Matching Pennies -/

/-- The two players of Matching Pennies. -/
inductive MPPlayer : Type
  | row
  | col
  deriving DecidableEq, Fintype

/-- The two available moves. -/
inductive MPMove : Type
  | heads
  | tails
  deriving DecidableEq, Fintype

/-- Both players choose among the same two moves. -/
abbrev MPStrategy : MPPlayer → Type := fun _ => MPMove

instance : DecidableEq (Profile MPStrategy) := by
  unfold Profile MPStrategy; infer_instance

instance : Fintype (Profile MPStrategy) := by
  unfold Profile MPStrategy; infer_instance

instance : Nonempty (Profile MPStrategy) := ⟨fun _ => MPMove.heads⟩

/-- Payoffs of Matching Pennies.  Row earns `1` when the two moves match and
`-1` otherwise; Column earns the opposite. -/
def matchingPenniesPayoff : MPPlayer → Profile MPStrategy → ℝ :=
  fun player p =>
    match player with
    | .row => if p .row = p .col then 1 else -1
    | .col => if p .row = p .col then -1 else 1



end PotentialGames


