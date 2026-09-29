-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_finrank_braidFlat
-- name    : Geometry.KernelPatterns.finrank_braidFlat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:21:39.279778+00:00
-- url     : https://prove2.me/theorems/2ac5db1f-3830-40da-8231-4d493d3768dd
-- title:
--   The dimension of a braid flat is the number of blocks of the kernel.
-- statement:
--   **The dimension of a braid flat is the number of blocks of the kernel.**
--
--   ```lean
--   theorem Geometry.KernelPatterns.finrank_braidFlat[DecidableEq X] (x : Fin n → X) :
--       Module.finrank ℝ (braidFlat x) = (univ.image (pat x)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/BraidFlats.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/BraidFlats.lean#L107

-- Thm stub generated from Geometry/KernelPatterns/BraidFlats.lean
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

theorem Geometry.KernelPatterns.finrank_braidFlat[DecidableEq X] (x : Fin n → X) :
    Module.finrank ℝ (braidFlat x) = (univ.image (pat x)).card := by sorry
