-- Prove2me | Definitions.Def_Geometry_KnotTheory_Defs
-- name    : Geometry_KnotTheory_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:37.2677+00:00
-- url     : https://prove2.me/theorems/041595c2-da7b-4a63-bfe4-a3c00fa38467
-- title:
--   Aether Catalog definitions — Geometry_KnotTheory_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KnotTheory.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KnotTheory/Defs.lean by skeleton subtraction
import Mathlib
/-
  # Foundations for the Kauffman bracket

  This file provides the combinatorial data underlying the Kauffman bracket state
  sum: smoothings of crossings, smoothing states of a diagram, the loop-count of a
  smoothed diagram, and the three Reidemeister moves recorded through their effect
  on the loop-count.

  A crossing may be resolved in one of two ways, an `A`-smoothing or a
  `B`-smoothing.  A *state* of an `n`-crossing diagram is a choice of smoothing at
  each crossing, i.e. a function `Fin n → Smoothing`.  A link diagram additionally
  records, for each state, the number of disjoint loops in the fully smoothed
  picture (always at least one).  Oriented diagrams carry a writhe.

  The Reidemeister moves are encoded structurally through the way the loop-count of
  the larger diagram relates to that of the smaller one under the two possible
  smoothings of the crossing that the move creates or removes.
-/

/-!
-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): A finite state-sum treatment of knot polynomials can
separate the combinatorics of smoothing choices from the geometric assertion
that a Reidemeister move preserves the relevant loop data.
Experiment (Experimenter): smoothing states were represented by functions on a
finite crossing set, and the first and third Reidemeister moves were expressed
through their exact effects on loop counts and writhe.
Analysis (Analyst): the identity `numA + numB = n` is the basic conservation law
needed to transfer preservation of one smoothing count to the other.
Critique (Critic): `LinkDiagram` records only the data needed by these state-sum
arguments; it is not claimed to encode planar embeddings or ambient isotopy.
Synthesis (Principal Investigator): these definitions provide a reusable finite
combinatorial foundation for bracket calculations and for comparison with
signed lattice-state generating functions.
-- !-- End Lab Notes -- !--
-/

namespace Knot

open Finset

/-- A crossing is resolved by one of two smoothings. -/
inductive Smoothing
  | A
  | B
deriving DecidableEq, Fintype

/-- A smoothing state of an `n`-crossing diagram: a choice of smoothing at each
crossing. -/
abbrev KState (n : ℕ) := Fin n → Smoothing

/-- The number of `A`-smoothings in a state. -/
def numA {n : ℕ} (s : KState n) : ℕ :=
  (Finset.univ.filter (fun i => s i = Smoothing.A)).card

/-- The number of `B`-smoothings in a state. -/
def numB {n : ℕ} (s : KState n) : ℕ :=
  (Finset.univ.filter (fun i => s i = Smoothing.B)).card


/-- A link diagram on `n` crossings, recorded through the loop-count of each of its
smoothing states.  A fully smoothed diagram always has at least one loop. -/
structure LinkDiagram (n : ℕ) where
  /-- The number of loops in the diagram smoothed according to a given state. -/
  loops : KState n → ℕ
  /-- A smoothed diagram has at least one loop. -/
  loops_pos : ∀ s, 0 < loops s

/-- An oriented link diagram additionally records a writhe. -/
structure OrientedLinkDiagram (n : ℕ) extends LinkDiagram n where
  /-- The writhe (signed crossing count) of the oriented diagram. -/
  writhe : ℤ

/-- The unknot, drawn with no crossings: a single loop. -/
def unknotDiagram : LinkDiagram 0 where
  loops := fun _ => 1
  loops_pos := fun _ => Nat.one_pos




end Knot


