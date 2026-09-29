-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_finrank_braidFlat_const
-- name    : Geometry.KernelPatterns.finrank_braidFlat_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:21:42.552674+00:00
-- url     : https://prove2.me/theorems/b88cb5a5-bdb8-4af7-a5eb-c57fd22fdb5a
-- title:
--   Extreme cases: a constant tuple cuts out the line of constant vectors, of
-- statement:
--   Extreme cases: a constant tuple cuts out the line of constant vectors, of
--   dimension `1` when `n ≠ 0`.
--
--   ```lean
--   theorem Geometry.KernelPatterns.finrank_braidFlat_const[NeZero n] (c : X) :
--       Module.finrank ℝ (braidFlat (fun _ : Fin n => c)) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/BraidFlats.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/BraidFlats.lean#L119

-- Thm stub generated from Geometry/KernelPatterns/BraidFlats.lean
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

theorem Geometry.KernelPatterns.finrank_braidFlat_const[NeZero n] (c : X) :
    Module.finrank ℝ (braidFlat (fun _ : Fin n => c)) = 1 := by sorry
