-- Prove2me | solution 1 for Geometry.KernelPatterns.braidFlat_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:47:47.193555+00:00
-- url     : https://prove2.me/submissions/b660b6c1-2af8-43a9-9503-51b57904a74a

-- Sol generated from Geometry/KernelPatterns/BraidFlats.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
import Definitions.Def_Geometry_KernelPatterns_Core
import Theorems.Thm_Geometry_KernelPatterns_braidFlat_le_iff

/-!
# Kernel patterns as the flats of the braid arrangement

The braid arrangement `A_{n-1}` in `ℝ^n` is the family of hyperplanes
`H_{ij} = {v | v i = v j}`.  Its *flats* (the elements of its intersection
lattice) are the subspaces obtained by intersecting families of these
hyperplanes; each such subspace is cut out by the equations coming from an
equivalence relation on the index set.

This file is the geometric side of `Geometry.KernelPatterns.Core`:

* `braidFlat x` — the flat cut out by the kernel of the tuple `x`.
* `braidFlat_eq_iff` — **two tuples cut out the same flat iff they have the
  same kernel pattern**, so `pat` is a complete invariant of the flat.
* `braidFlat_le_iff` — the (order-reversing) dictionary between inclusion of
  flats and refinement of kernels.
* `finrank_braidFlat` — the dimension of the flat is the number of blocks.
* `card_braidFlats` — the intersection lattice of the braid arrangement has
  exactly `(patterns n n).card` elements; for `n ≤ 5` this is the Bell number
  (`card_braidFlats_five : ... = 52`).
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X : Type*}











/-! ### Counting the flats -/






open Geometry.KernelPatterns in
theorem solution[DecidableEq X] {Y : Type*} [DecidableEq Y]
    (x : Fin n → X) (y : Fin n → Y) :
    braidFlat x = braidFlat y ↔ pat x = pat y := by
  constructor
  · intro h
    refine pat_congr fun k l => ?_
    have h1 := (braidFlat_le_iff y x).1 h.ge
    have h2 := (braidFlat_le_iff x y).1 h.le
    exact ⟨fun hkl => h1 k l hkl, fun hkl => h2 k l hkl⟩
  · intro h
    have hker : ∀ i j, x i = x j ↔ y i = y j := by
      intro i j
      rw [← pat_eq_iff (x := x), ← pat_eq_iff (x := y), h]
    apply le_antisymm
    · exact (braidFlat_le_iff x y).2 fun i j hy => (hker i j).2 hy
    · exact (braidFlat_le_iff y x).2 fun i j hx => (hker i j).1 hx
