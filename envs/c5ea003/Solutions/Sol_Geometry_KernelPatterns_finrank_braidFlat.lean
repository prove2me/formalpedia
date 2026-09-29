-- Prove2me | solution 1 for Geometry.KernelPatterns.finrank_braidFlat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:41.484405+00:00
-- url     : https://prove2.me/submissions/1604825e-ac69-4433-a20f-95b91daf3c7d

-- Sol generated from Geometry/KernelPatterns/BraidFlats.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
import Definitions.Def_Geometry_KernelPatterns_Core

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
theorem solution[DecidableEq X] (x : Fin n → X) :
    Module.finrank ℝ (braidFlat x) = (univ.image (pat x)).card := by
  rw [(braidFlatEquiv x).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]
