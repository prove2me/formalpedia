-- Prove2me | solution 1 for Geometry.KernelPatterns.card_braidFlats
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:34.407306+00:00
-- url     : https://prove2.me/submissions/7bcc370e-b462-4891-876e-1a219dbf9d82

-- Sol generated from Geometry/KernelPatterns/BraidFlats.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
import Definitions.Def_Geometry_KernelPatterns_Core
import Theorems.Thm_Geometry_KernelPatterns_braidFlat_eq_iff

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
theorem solution(n : ℕ) : Nat.card (braidFlats n) = (patterns n n).card := by
  classical
  have hbij : Function.Bijective
      (fun p : ↥(patterns n n) => (⟨braidFlat (p : Fin n → Fin n), ⟨p, rfl⟩⟩ :
        ↥(braidFlats n))) := by
    constructor
    · rintro ⟨p, hp⟩ ⟨q, hq⟩ h
      rw [mem_patterns_self] at hp hq
      have : braidFlat p = braidFlat q := congrArg Subtype.val h
      have := (braidFlat_eq_iff p q).1 this
      rw [hp, hq] at this
      exact Subtype.ext this
    · rintro ⟨L, x, rfl⟩
      refine ⟨⟨pat x, (mem_patterns_self _).2 (pat_idem x)⟩, Subtype.ext ?_⟩
      exact (braidFlat_eq_iff (pat x) x).2 (pat_idem x)
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_finsetCard]
