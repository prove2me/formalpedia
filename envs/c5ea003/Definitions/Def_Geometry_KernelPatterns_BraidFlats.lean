-- Prove2me | Definitions.Def_Geometry_KernelPatterns_BraidFlats
-- name    : Geometry_KernelPatterns_BraidFlats
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:37:06.533413+00:00
-- url     : https://prove2.me/theorems/c5ffae21-b8de-4983-b8ac-bedee5afa857
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_BraidFlats
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.BraidFlats`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/BraidFlats.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
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

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X : Type*}

/-- The flat of the braid arrangement determined by the kernel of a tuple `x`:
the set of vectors constant on the blocks of `x`. -/
def braidFlat (x : Fin n → X) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ i j, x i = x j → v i = v j}
  add_mem' := by intro a b ha hb i j h; simp [ha i j h, hb i j h]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by intro c a ha i j h; simp [ha i j h]


/-- The characteristic vector of the block of `i`. -/
def blockIndicator [DecidableEq X] (x : Fin n → X) (i : Fin n) : Fin n → ℝ :=
  fun k => if x k = x i then 1 else 0




/-- Coordinates on a flat: a vector constant on blocks is exactly a function on
the set of first-occurrence representatives. -/
noncomputable def braidFlatEquiv [DecidableEq X] (x : Fin n → X) :
    braidFlat x ≃ₗ[ℝ] (↥(univ.image (pat x)) → ℝ) where
  toFun v := fun r => (v : Fin n → ℝ) r.1
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl
  invFun w := ⟨fun i => w ⟨pat x i, Finset.mem_image_of_mem _ (mem_univ i)⟩, by
    intro i j h
    have : pat x i = pat x j := pat_eq_iff.2 h
    simp [this]⟩
  left_inv := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    funext i
    exact hv _ _ (apply_pat x i)
  right_inv := by
    intro w
    funext r
    obtain ⟨r, hr⟩ := r
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
    simp




/-! ### Counting the flats -/

/-- The intersection lattice of the braid arrangement: the flats cut out by
`n`-tuples. -/
def braidFlats (n : ℕ) : Set (Submodule ℝ (Fin n → ℝ)) :=
  {L | ∃ x : Fin n → Fin n, L = braidFlat x}




end Geometry.KernelPatterns


