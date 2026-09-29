-- Prove2me | Definitions.Def_Novelty_SchubertSmoothPatterns
-- name    : Novelty_SchubertSmoothPatterns
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:12.6694+00:00
-- url     : https://prove2.me/theorems/4184af09-1be0-4d72-91c5-9104ea476bbd
-- title:
--   Aether Catalog definitions — Novelty_SchubertSmoothPatterns
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SchubertSmoothPatterns`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SchubertSmoothPatterns.lean by skeleton subtraction
import Mathlib

/-!
# Smooth permutations and the 3412/4231 pattern-avoidance core of Schubert geometry

This file formalizes the *combinatorial heart* of the conjecture studied in this research
mission:

> *The multigraded Castelnuovo–Mumford regularity of a Schubert variety `S_σ` in the Plücker
> embedding is controlled by chains of Bruhat-ordered Schubert varieties whose every step is
> a `3412`/`4231`-avoiding element.*

The avoidance of the two length-4 patterns `3412` and `4231` is exactly the
Lakshmibai–Sandhya smoothness criterion for Schubert varieties.  The deep algebraic geometry
(regularity, Plücker embeddings) is not available in Mathlib, so we isolate and prove the
purely combinatorial statements that the conjecture rests on: which permutations are smooth,
why the family is closed under the standard symmetries, and a structural dichotomy for small
rank.

A *pattern* of length 4 is given by its one-line word as a function `Fin 4 → Fin 4`
(0-indexed: `3412 ↦ ![2,3,0,1]`, `4231 ↦ ![3,1,2,0]`).  A permutation `σ` of `Fin n`
*contains* the pattern `π` when some strictly increasing list of four positions carries the
same relative order as `π`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The smooth class (avoid 3412 and 4231) is a genuine, robust
  combinatorial family, closed under the natural involutive symmetries of `S_n` (inverse,
  reverse) and trivial below rank 4.
Experiment (Experimenter): Enumerated smooth permutations of `{1..n}` for n ≤ 7, obtaining
  6, 22, 88, 366, 1552 (n = 3..7) — OEIS A005802, the Schubert-smooth sequence.  Then proved
  the structural facts below over `Equiv.Perm (Fin n)`.
Analysis (Analyst): Identity and the longest element `w₀` (reverse) are *both* smooth: the
  identity only contains the increasing pattern, the reverse only contains the decreasing
  pattern, and neither 3412 nor 4231 is monotone.  Below rank 4 there is no room for a
  length-4 pattern, so smoothness is automatic — this is the combinatorial shadow of "all
  Schubert varieties in `Fl(≤3)` are smooth".
Critique (Critic): Avoidance is defined as a genuine `¬ ∃` statement (not vacuous): for n ≥ 4
  the witnessing embeddings exist, so the theorems have real content; we additionally exhibit
  the patterns as honest non-identity, non-reverse permutations.
Synthesis (PI): The smooth family is pinned down by `idPerm_avoids_*`, `revPerm_avoids_*`,
  `smooth_of_lt_four`, packaged through the predicate `IsSmooth`.
-- !-- Lab Notes -- !--
-/

namespace SchubertSmooth

open Equiv

/-- `Contains σ π` : the permutation `σ` of `Fin n` contains the length-4 pattern
`π : Fin 4 → Fin 4`, i.e. there are four strictly increasing positions on which `σ` realizes
the same relative order as `π`. -/
def Contains {n : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin 4 → Fin 4) : Prop :=
  ∃ f : Fin 4 → Fin n, StrictMono f ∧ ∀ a b : Fin 4, (σ (f a) < σ (f b) ↔ π a < π b)

/-- `Avoids σ π` : `σ` does not contain the pattern `π`. -/
def Avoids {n : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin 4 → Fin 4) : Prop := ¬ Contains σ π

/-- The pattern `3412` (one-line word, 0-indexed). -/
def pat3412 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The pattern `4231` (one-line word, 0-indexed). -/
def pat4231 : Fin 4 → Fin 4 := ![3, 1, 2, 0]

/-- A permutation is *smooth* when it avoids both `3412` and `4231`
(the Lakshmibai–Sandhya criterion). -/
def IsSmooth {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Avoids σ pat3412 ∧ Avoids σ pat4231



/-
Containing a length-4 pattern forces the ambient rank to be at least 4.
-/

/-
Below rank 4 every permutation avoids every length-4 pattern: all small Schubert
varieties are smooth.
-/

/-
Below rank 4 every permutation is smooth.
-/

/-
The identity avoids `3412`.
-/

/-
The identity avoids `4231`.
-/


/-
The reverse (longest element `w₀`) avoids `3412`.
-/

/-
The reverse (longest element `w₀`) avoids `4231`.
-/


end SchubertSmooth


