-- Prove2me | Definitions.Def_Bridges_PosetTheory_ProofDAGStructure
-- name    : Bridges_PosetTheory_ProofDAGStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:13.533491+00:00
-- url     : https://prove2.me/theorems/dda8e3ea-88cf-41c5-a8ae-0dae4bcc6a14
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_ProofDAGStructure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.ProofDAGStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/ProofDAGStructure.lean by skeleton subtraction
import Mathlib

/-!
# Ranked Dependency Networks: Width, Depth, and Robustness

A dependency network is represented by a relation `R`, oriented from a premise to a
statement using that premise.  Acyclicity means that the transitive closure has no
self-loop.  This development separates three structural facts from empirical claims
about large mathematical corpora.

First, every finite acyclic network has a canonical topological rank: the number of
strict ancestors.  Second, combining this rank with the pigeonhole principle gives a
width–depth theorem: if there are more statements than available rank levels, two
statements on one level are incomparable.  Third, a family of totally ordered dependency
networks remains weakly connected after deletion of any one nonterminal vertex.  Thus
acyclicity alone neither implies a power law nor universal hub-removal fragility.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): finite acyclicity should force a topological hierarchy, but
neither a heavy-tailed degree law nor articulation hubs.  A depth bound should instead
force width by a pigeonhole argument.

Experiment (Experimenter): rank each node by the cardinality of its transitive
predecessor set; test deletion on strict total-order networks, where every surviving
pair remains joined by a direct edge in one orientation.

Analysis (Analyst): reachability strictly enlarges predecessor sets, producing the
ranking.  Bounded ranks then create an incomparable pair whenever the vertex count
exceeds the number of levels.  Total-order networks provide robust acyclic examples,
contradicting any graph-theoretic derivation of fragility from acyclicity alone.

Critique (Critic): the results do not estimate a degree-distribution exponent and do
not identify historical theorems as hubs; those are empirical questions requiring a
specified corpus and dependency extraction policy.  Connectivity is explicitly weak
connectivity of the surviving directed network, avoiding an ambiguous use of
"disconnects".  Nonemptiness and cardinality hypotheses prevent vacuity.

Synthesis (Principal Investigator): finite proof structure yields a rigorous
order-theoretic width–depth law, while a concrete robust family establishes the boundary
between structural theorem and corpus-dependent hypothesis.
-- !-- end Lab Notes -- !--
-/

open scoped Classical

namespace ProofDAGStructure

variable {V : Type*}

/-- A direct dependency relation is acyclic when its nonempty transitive closure is
irreflexive. -/
def Acyclic (R : V → V → Prop) : Prop := ∀ v, ¬ Relation.TransGen R v v

/-- The strict ancestors of a node in a finite dependency network. -/
noncomputable def ancestors [Fintype V] (R : V → V → Prop) (v : V) : Finset V :=
  Finset.univ.filter (fun u => Relation.TransGen R u v)

/-
Reachability carries every ancestor of the source to an ancestor of the target.
-/

/-
Along a dependency chain, the ancestor set grows strictly.
-/

/-
Every finite acyclic dependency network has a canonical topological numbering,
given by the number of strict ancestors.
-/

/-
A bounded topological ranking with fewer levels than vertices forces two distinct,
mutually incomparable statements on the same level.  This is a width–depth tradeoff
obtained by bridging acyclic order structure with the finite pigeonhole principle.
-/

/-- Weak reachability while avoiding a deleted vertex: each step may follow a dependency
edge in either direction, and every visited endpoint must survive. -/
inductive AvoidingWalk (R : V → V → Prop) (deleted : V) : V → V → Prop
  | refl {a} (ha : a ≠ deleted) : AvoidingWalk R deleted a a
  | step {a b c} (ha : a ≠ deleted) (hab : R a b ∨ R b a)
      (hbc : AvoidingWalk R deleted b c) : AvoidingWalk R deleted a c

/-- The strict total-order dependency network on `Fin n`. -/
def totalOrderDAG (n : ℕ) : Fin n → Fin n → Prop := fun i j => i < j

/-
Strict total-order dependency networks are acyclic.
-/

/-
Deleting any vertex from a total-order dependency network leaves all surviving
vertices weakly connected.  This gives an infinite family of acyclic networks with no
single-vertex weak-connectivity fragility.
-/

/-
In particular, for every size at least three there is a nontrivial acyclic network,
with three distinct named vertices, whose deletion at an arbitrary vertex preserves weak
connectivity among all survivors.
-/

end ProofDAGStructure


