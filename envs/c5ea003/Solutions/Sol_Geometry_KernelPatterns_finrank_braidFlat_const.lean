-- Prove2me | solution 1 for Geometry.KernelPatterns.finrank_braidFlat_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:12:49.939655+00:00
-- url     : https://prove2.me/submissions/13f7ec19-775d-45b3-877b-5a3a45cca51e

-- Sol generated from Geometry/KernelPatterns/BraidFlats.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
import Definitions.Def_Geometry_KernelPatterns_Core
import Theorems.Thm_Geometry_KernelPatterns_finrank_braidFlat

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
theorem solution[NeZero n] (c : X) :
    Module.finrank ℝ (braidFlat (fun _ : Fin n => c)) = 1 := by
  classical
  rw [finrank_braidFlat]
  have h0 : ∀ i : Fin n, pat (fun _ : Fin n => c) i = (0 : Fin n) := by
    intro i
    have hle : pat (fun _ : Fin n => c) i ≤ (0 : Fin n) := Finset.min'_le _ _ (by simp)
    have hval : (pat (fun _ : Fin n => c) i : ℕ) ≤ ((0 : Fin n) : ℕ) := hle
    have h00 : ((0 : Fin n) : ℕ) = 0 := rfl
    exact Fin.ext (by omega)
  have himg : univ.image (pat fun _ : Fin n => c) = {(0 : Fin n)} := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩; exact h0 i
    · rintro rfl; exact ⟨(0 : Fin n), h0 _⟩
  rw [himg, Finset.card_singleton]
