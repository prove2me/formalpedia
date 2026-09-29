-- Prove2me | Definitions.Def_Novelty_Homology
-- name    : Novelty_Homology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:41.538983+00:00
-- url     : https://prove2.me/theorems/c6486ae8-3830-4521-b106-3f5c01c07078
-- title:
--   Aether Catalog definitions — Novelty_Homology
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Homology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Homology.lean by skeleton subtraction
import Mathlib
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
/-
# Homotopy / homology obstruction toolkit

This file packages the algebraic-topological invariant that detects the
obstruction in the line-transversal classification.

The geometric obstruction to the transversal space having the homotopy type of a
sphere lives in the *first homology group of the configuration space*.  In Mathlib
the available homotopy invariant at this level is the **fundamental groupoid**,
whose abelianization is exactly the first homology group `H₁` (Hurewicz).  The key
fact we re-export is that a homotopy equivalence induces an *equivalence of
fundamental groupoids*; consequently any homotopy invariant computed from the
fundamental groupoid (in particular `H₁`) agrees on homotopy-equivalent spaces.

We use this in `FINAL.LineTransversal` to phrase the obstruction: if the
transversal space had the homotopy type of the sphere, its fundamental groupoid —
and hence its first homology group — would coincide with that of the sphere.
-/

open scoped ContinuousMap
open CategoryTheory

namespace FINAL.Homology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The fundamental groupoid of a topological space, as the value of Mathlib's
fundamental-groupoid functor.  Its abelianization is the first singular homology
group `H₁`. -/
noncomputable abbrev fundamentalGroupoidObj (X : Type*) [TopologicalSpace X] :=
  FundamentalGroupoid.fundamentalGroupoidFunctor.obj ⟨X⟩


end FINAL.Homology


