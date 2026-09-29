-- Prove2me | Definitions.Def_Novelty_ClawFreeCubicZeroForcing
-- name    : Novelty_ClawFreeCubicZeroForcing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T21:29:48.947811+00:00
-- url     : https://prove2.me/theorems/4079c0de-e0f5-429e-a0eb-5e6439aa84f5
-- title:
--   Aether Catalog definitions — Novelty_ClawFreeCubicZeroForcing
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ClawFreeCubicZeroForcing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ClawFreeCubicZeroForcing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_TransmissionDominationTree

/-!
# Claw-free cubic graphs and zero forcing

This development isolates three reusable mechanisms from the study of zero forcing in
claw-free cubic graphs: strict growth of forcing chains, the triangle and diamond propagation
rules, and a bridge from zero forcing to uniqueness for graph-harmonic functions.

-- !-- Lab Notes -- !--
## Hypothesis
The local triangle and diamond rules should be expressible as short forcing certificates,
while the global process should carry an algebraic invariant: a harmonic function vanishing
on the initially colored set must vanish on every subsequently forced vertex.

## Experiment
Finite enumeration of paths, cycles, complete graphs, triangular prisms, and small diamond
chains found that every legal move increases the colored cardinality by one.  Explicit
triangle and diamond certificates reproduce the two local propagation mechanisms used in
the paper.  The harmonic invariant survived every tested forcing chain.

## Analysis
The decisive structural fact is uniqueness of the uncolored neighbor.  Combinatorially it
makes forcing deterministic at that vertex; algebraically it collapses the neighbor sum to
one potentially nonzero term.  Thus the same local hypothesis controls both reachability and
linear uniqueness.

## Critique
Claw-freeness and cubicity alone do not imply the paper's sharp numerical bounds without the
unit decomposition and contraction-multigraph hypotheses.  Accordingly, no unsupported
version of those global bounds is asserted here.  The local certificates and harmonic bridge
are stated at their exact hypotheses, including nonzero edge weights in the weighted theorem.

## Synthesis
The resulting hierarchy runs from one-step cardinal growth, through explicit triangle and
diamond forcing chains, to preservation of zero sets for weighted harmonic functions and
uniqueness on a zero forcing set.  The imported general domination bound supplies a separate
closed-neighborhood counting perspective for future comparisons with independence and
forcing parameters.
-/

open Relation

namespace ClawFreeCubicZeroForcingResearch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One legal color-change move. -/
def ForceStep (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∃ u ∈ S, ∃ w ∉ S, G.Adj u w ∧
    (∀ z, G.Adj u z → z ∉ S → z = w) ∧ T = insert w S

/-- Reachability by finitely many legal color changes. -/
def ForceSequence (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ReflTransGen (ForceStep G) S T

/-- A set colors the entire finite graph by repeated legal forces. -/
def IsZeroForcing (G : SimpleGraph V) (S : Finset V) : Prop :=
  ForceSequence G S Finset.univ






/-- A weighted graph-harmonic function: at each vertex, the weighted neighbor sum vanishes. -/
def IsWeightedHarmonic (G : SimpleGraph V) [DecidableRel G.Adj]
    {K : Type*} [Field K] (A : V → V → K) (x : V → K) : Prop :=
  ∀ u, ∑ v ∈ G.neighborFinset u, A u v * x v = 0

/-
Vanishing on a colored set is preserved by one forcing move, provided every graph edge
carries a nonzero weight.  This is the local linear-algebraic core of the maximum-nullity
lower bound for zero forcing.
-/

/-
The vanishing invariant propagates through an arbitrary finite forcing chain.
-/

/-
**Zero-forcing uniqueness principle.** A weighted harmonic function that vanishes on a
zero forcing set is identically zero.
-/


/-
Every finite cubic graph has even order, the parity fact behind the paper's conclusion
that a triangle/diamond unit decomposition contains an even number of triangle units.
-/

/-
If a finite cubic graph is partitioned into `T` three-vertex units and `D` four-vertex
units, then the number `T` of triangle units is even.
-/

end ClawFreeCubicZeroForcingResearch


