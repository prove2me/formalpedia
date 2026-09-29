-- Prove2me | Definitions.Def_Novelty_Defs
-- name    : Novelty_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:02.074566+00:00
-- url     : https://prove2.me/theorems/3cf2c4a6-cdcb-4d6e-9652-d2bc7eb1e0b8
-- title:
--   Aether Catalog definitions — Novelty_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Defs.lean by skeleton subtraction
import Mathlib

/-!
# Minimal obstructions to total rainbow forests — core definitions

An *edge-colored graph* is a `SimpleGraph V` together with a colouring
`col : Sym2 V → κ` of its (potential) edges.  We study the following global
property, which we call *admitting a total rainbow forest*:

> every colour class of `G` is a forest (acyclic),

equivalently (see `Catalog.Novelty.TotalRainbowForest.ColorClass`):

> `G` contains **no monochromatic cycle**.

The name is justified by the colour-class characterisation
`admitsTRF_iff_forall_colorClass_acyclic`: `G` admits a total rainbow forest
exactly when its edges decompose, colour by colour, into forests, so that the
whole edge set is "totally" covered by a family of single-colour forests.

The central object is a *minimal obstruction*: a colouring with a monochromatic
cycle such that deleting **any** edge destroys every monochromatic cycle.  The
structure theorem (`Structure.lean`) shows a minimal obstruction is always a
single monochromatic cycle together with isolated vertices.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):
  H1. A minimal obstruction to "no monochromatic cycle" is a single monochromatic
      cycle plus isolated vertices.  [TRUE — proved in Structure.lean]
  H2. "Admits a total rainbow forest" is definition-sensitive.  Under the naive
      "rainbow *spanning* forest" reading (a spanning maximal forest with all
      edges of distinct colours), even a monochromatic *path* `P_3` is a minimal
      obstruction (its unique spanning tree is monochromatic, yet deleting either
      edge disconnects it so the remaining single edge is a rainbow spanning
      forest).  A path is not a cycle, so the literal conjecture is FALSE; the
      correct invariant is acyclicity of each colour class.  [motivates the defs]
  H3. For a monochromatic graph (all edges one colour) admitting a total rainbow
      forest is equivalent to being an ordinary forest.  [TRUE — ColorClass.lean]

Experiment (Experimenter):
  Small cases computed by hand (see ComputationalEvidence.md):
   * `C_3` monochromatic: one mono cycle; deleting any edge yields two edges =
     path = acyclic. Minimal obstruction. ✓
   * `C_n` monochromatic (n ≥ 3): same. ✓
   * two triangles sharing structure / a theta graph: NOT minimal (an edge off a
     given mono cycle can be deleted while keeping a mono cycle). ✓
   * `P_3` monochromatic: no mono cycle, so `AdmitsTRF` holds (it is a forest). ✓
-/

namespace Catalog.Novelty.TotalRainbowForest

open SimpleGraph

variable {V : Type*} {κ : Type*}

/-- A walk is **monochromatic** for the colouring `col` if all of its edges
receive a single colour. -/
def MonoWalk (col : Sym2 V → κ) {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Prop :=
  ∃ k, ∀ e ∈ p.edges, col e = k

/-- `G` **has a monochromatic cycle** for `col`: some cyclic walk has all its
edges of one colour. -/
def HasMonoCycle (G : SimpleGraph V) (col : Sym2 V → κ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ MonoWalk col c

/-- `G` **admits a total rainbow forest** for `col`: it has no monochromatic
cycle.  (Equivalently every colour class is a forest — see `ColorClass.lean`.) -/
def AdmitsTRF (G : SimpleGraph V) (col : Sym2 V → κ) : Prop :=
  ¬ HasMonoCycle G col



/-- The **colour class** of colour `k`: the subgraph of `G` consisting of edges
coloured `k`. -/
def colorClass (G : SimpleGraph V) (col : Sym2 V → κ) (k : κ) : SimpleGraph V :=
  G ⊓ fromEdgeSet {e | col e = k}



end Catalog.Novelty.TotalRainbowForest


