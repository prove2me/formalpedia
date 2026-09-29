-- Prove2me | Definitions.Def_Bridges_GraphTheory_SemicubeHelly
-- name    : Bridges_GraphTheory_SemicubeHelly
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:31.781559+00:00
-- url     : https://prove2.me/theorems/4d8b7f60-7a16-4998-88ce-54e70eb6a126
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_SemicubeHelly
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.SemicubeHelly`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/SemicubeHelly.lean by skeleton subtraction
import Mathlib
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

/-- The semicube determined by coordinate `i : ι` and bit `b : Bool`: the finite set of all
vertices (encoded as `Finset ι`) whose `i`-th coordinate equals `b`. -/
def semicube (ι : Type*) [Fintype ι] [DecidableEq ι] (i : ι) (b : Bool) : Finset (Finset ι) :=
  Finset.univ.filter (fun s => decide (i ∈ s) = b)


