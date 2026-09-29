-- Prove2me | Definitions.Def_Tropical_DeltaMatroid_Twist
-- name    : Tropical_DeltaMatroid_Twist
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:02.397282+00:00
-- url     : https://prove2.me/theorems/393eb1da-99c2-4dbb-9340-93ecfaa65182
-- title:
--   Aether Catalog definitions — Tropical_DeltaMatroid_Twist
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.DeltaMatroid.Twist`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/DeltaMatroid/Twist.lean by skeleton subtraction
import Mathlib

/-!
# Twist (partial twuality) on set systems and the Bouchet closure theorem

This file develops the algebra of the *twist* operation `D ↦ D * A` on set systems,
the elementary operation underlying *partial twuality* of (binary) delta-matroids
in the sense of Chmutov, Gross–Mansour–Tucker and Yan–Jin.

A **set system** on a finite ground set is a finite collection `D : Finset (Finset α)`
of feasible subsets.  The **twist by `A`** sends each feasible set `F` to the symmetric
difference `F ∆ A`.  This is the combinatorial core of partial duality of ribbon
graphs (Chmutov) and of partial twuality of delta-matroids (Yan–Jin).

Main results:
* `twist_empty`, `twist_twist`, `twist_involutive`: the twists form an action of the
  symmetric–difference group `(Finset α, ∆)` on set systems (the "categorical
  structure" mentioned in the mission framing).
* `twist_symExchange`: **the class of delta-matroids is closed under twist** —
  if a set system satisfies Bouchet's symmetric–exchange axiom, so does every twist
  of it.  This is the foundational closure theorem that makes partial twuality
  well defined on delta-matroids.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The twist operation `* A` is an involution and the family
  `{* A}` is a group action of `(2^E, ∆)`; moreover delta-matroids are closed under it.
Experiment (Experimenter): Formalised `twist`, `SymExchange`; proved the group-action
  laws and the closure theorem.  Key algebraic fact: `(F₁ ∆ A) ∆ (F₂ ∆ A) = F₁ ∆ F₂`,
  so the exchange data transports verbatim through a twist.
Analysis (Analyst): The closure proof is *definition-driven*: the `A` cancels in every
  pairwise symmetric difference, so the witness `y` for the original system also works
  for the twisted system.  Survived: all four theorems.
Critique (Critic): Statements are non-vacuous (see `Examples.lean` for an explicit
  delta-matroid where `SymExchange` is verified independently and then twisted).
  No theorem is `True`/`rfl`-only; `twist_symExchange` uses real `obtain`/`refine`
  case analysis on the exchange witness.
Synthesis (PI): These laws license treating the partial-twuality polynomial as an
  invariant of a *twist orbit*, exploited in `Interpolation.lean`.
-/

open Finset
open scoped symmDiff

namespace DeltaMatroid

variable {α : Type*} [DecidableEq α]

/-- The twist (partial twuality elementary move) of a set system `D` by a subset `A`:
each feasible set `F` is replaced by `F ∆ A`. -/
def twist (A : Finset α) (D : Finset (Finset α)) : Finset (Finset α) := D.image (· ∆ A)

/-- Bouchet's **symmetric exchange axiom**: the defining property of a delta-matroid.
For all feasible `F₁, F₂` and every `x` in their symmetric difference, there is a
`y` (possibly equal to `x`) in the symmetric difference with `F₁ ∆ {x, y}` feasible. -/
def SymExchange (D : Finset (Finset α)) : Prop :=
  ∀ F1 ∈ D, ∀ F2 ∈ D, ∀ x ∈ F1 ∆ F2, ∃ y ∈ F1 ∆ F2, F1 ∆ ({x, y} : Finset α) ∈ D





end DeltaMatroid


