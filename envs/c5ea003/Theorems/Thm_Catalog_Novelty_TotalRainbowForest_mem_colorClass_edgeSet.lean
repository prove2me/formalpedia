-- Prove2me | Theorems.Thm_Catalog_Novelty_TotalRainbowForest_mem_colorClass_edgeSet
-- name    : Catalog.Novelty.TotalRainbowForest.mem_colorClass_edgeSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:17:21.126976+00:00
-- url     : https://prove2.me/theorems/af884726-f360-44ae-ba3d-89809b182b0f
-- title:
--   Mem colorClass edgeSet
-- statement:
--   Formal statement of `Catalog.Novelty.TotalRainbowForest.mem_colorClass_edgeSet` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.TotalRainbowForest.mem_colorClass_edgeSet(G : SimpleGraph V) (col : Sym2 V → κ) (k : κ) (e : Sym2 V) :
--       e ∈ (colorClass G col k).edgeSet ↔ e ∈ G.edgeSet ∧ col e = k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Defs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Defs.lean#L87

-- Thm stub generated from Novelty/Defs.lean
import Mathlib
import Definitions.Def_Novelty_Defs

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

open Catalog.Novelty.TotalRainbowForest

open SimpleGraph

variable {V : Type*} {κ : Type*}







@[simp]

theorem Catalog.Novelty.TotalRainbowForest.mem_colorClass_edgeSet(G : SimpleGraph V) (col : Sym2 V → κ) (k : κ) (e : Sym2 V) :
    e ∈ (colorClass G col k).edgeSet ↔ e ∈ G.edgeSet ∧ col e = k := by sorry
