-- Prove2me | solution 1 for semicube_helly2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:48:05.941634+00:00
-- url     : https://prove2.me/submissions/3524dff3-4ad5-48ca-ac4b-a17834916af7

-- Sol generated from Bridges/SemicubeHelly.lean
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


/-- For a fixed coordinate `i`, the semicube with bit `true` and the semicube with bit `false`
are disjoint: a vertex cannot have its `i`-th coordinate equal to both `true` and `false`. -/
lemma semicube_disjoint (i : ι) :
    Disjoint (semicube ι i true) (semicube ι i false) := by
  exact Finset.disjoint_filter.2 fun _ _ _ _ => by aesop



theorem solution(F : Finset (ι × Bool))
    (hpair : ∀ p ∈ F, ∀ q ∈ F, p ≠ q →
      (semicube ι p.1 p.2 ∩ semicube ι q.1 q.2).Nonempty) :
    (⋂ p ∈ F, (semicube ι p.1 p.2 : Set (Finset ι))).Nonempty := by
  -- Construct the witness vertex `v` as the set of coordinates where the bit is `true`.
  set v := Finset.univ.filter (fun i => (i, true) ∈ F) with hv_def
  refine ⟨v, ?_⟩
  simp +decide [hv_def, semicube]
  intro i hi₁ hi₂
  specialize hpair (i, true) hi₂ (i, false) hi₁
  simp_all +decide
  exact hpair.elim fun x hx => by
    have := semicube_disjoint i
    exact Finset.disjoint_left.mp this (Finset.mem_of_mem_inter_left hx)
      (Finset.mem_of_mem_inter_right hx)
