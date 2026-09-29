-- Prove2me | Theorems.Thm_semicube_helly2
-- name    : semicube_helly2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:28.64487+00:00
-- url     : https://prove2.me/theorems/e0befc3c-bd79-499c-84db-1caac5c2f033
-- title:
--   Helly number 2 for semicubes.
-- statement:
--   **Helly number 2 for semicubes.** If every pair of semicubes in a finite family `F` has a
--   common vertex, then the whole family has a common vertex.
--
--   ```lean
--   theorem semicube_helly2(F : Finset (ι × Bool))
--       (hpair : ∀ p ∈ F, ∀ q ∈ F, p ≠ q →
--         (semicube ι p.1 p.2 ∩ semicube ι q.1 q.2).Nonempty) :
--       (⋂ p ∈ F, (semicube ι p.1 p.2 : Set (Finset ι))).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/SemicubeHelly.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/SemicubeHelly.lean#L57

-- Thm stub generated from Bridges/SemicubeHelly.lean
import Mathlib
import Definitions.Def_Bridges_SemicubeHelly
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Helly number 2 for semicubes in finite hypercubes

Consider the hypercube `Q(ι)` for a finite type `ι` with decidable equality, whose vertices are
represented as elements of `Finset ι` (the set of coordinates where the vertex has value `true`).

A **semicube** determined by a coordinate `i : ι` and a bit `b : Bool` is the set of all vertices
whose `i`-th coordinate equals `b`.

We prove the **Helly number 2** property for semicubes: if a finite family of semicubes has the
property that every *pair* of members has a common vertex, then the *whole* family has a common
vertex.

## Main definitions

* `semicube` : the semicube determined by a coordinate and a bit.

## Main results

* `semicube_disjoint` : the two semicubes for a fixed coordinate (bits `true` and `false`) are
  disjoint.
* `semicube_agree` : in a pairwise-intersecting family, the bit attached to a coordinate is
  determined.
* `semicube_helly2` : the Helly number 2 property for semicubes.
-/

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem semicube_helly2(F : Finset (ι × Bool))
    (hpair : ∀ p ∈ F, ∀ q ∈ F, p ≠ q →
      (semicube ι p.1 p.2 ∩ semicube ι q.1 q.2).Nonempty) :
    (⋂ p ∈ F, (semicube ι p.1 p.2 : Set (Finset ι))).Nonempty := by sorry
