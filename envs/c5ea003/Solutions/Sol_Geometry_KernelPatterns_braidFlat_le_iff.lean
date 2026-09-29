-- Prove2me | solution 1 for Geometry.KernelPatterns.braidFlat_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:45:34.802372+00:00
-- url     : https://prove2.me/submissions/180d3bb0-5f10-414b-b961-973690b54a34

-- Sol generated from Geometry/KernelPatterns/BraidFlats.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_BraidFlats

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




lemma blockIndicator_mem [DecidableEq X] (x : Fin n → X) (i : Fin n) :
    blockIndicator x i ∈ braidFlat x := by
  intro k l h
  simp [blockIndicator, h]







/-! ### Counting the flats -/






open Geometry.KernelPatterns in
theorem solution[DecidableEq X] {Y : Type*} [DecidableEq Y]
    (x : Fin n → X) (y : Fin n → Y) :
    braidFlat x ≤ braidFlat y ↔ ∀ i j, y i = y j → x i = x j := by
  constructor
  · intro h i j hy
    have hmem : blockIndicator x i ∈ braidFlat y := h (blockIndicator_mem x i)
    have hval : (if x i = x i then (1 : ℝ) else 0) = (if x j = x i then (1 : ℝ) else 0) :=
      hmem i j hy
    rw [if_pos rfl] at hval
    by_contra hx
    rw [if_neg fun hji => hx hji.symm] at hval
    exact one_ne_zero hval
  · intro h v hv i j hy
    exact hv i j (h i j hy)
