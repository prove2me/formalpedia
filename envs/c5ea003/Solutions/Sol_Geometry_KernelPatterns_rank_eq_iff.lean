-- Prove2me | solution 1 for Geometry.KernelPatterns.rank_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:00:56.098165+00:00
-- url     : https://prove2.me/submissions/4c1853db-5287-41a0-aa57-fa559b90f66e

-- Sol generated from Geometry/KernelPatterns/Faces.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Faces
import Theorems.Thm_Geometry_KernelPatterns_rank_lt_iff

/-!
# Cycle 2: ordered patterns and the faces of the braid arrangement

A kernel pattern remembers which coordinates of a tuple agree; an *ordered*
pattern also remembers how the resulting blocks are ordered.  Geometrically,
kernel patterns index the flats of the braid arrangement while ordered patterns
index its **faces** (relatively open cones): the face containing `v` is cut out
by the full system of comparisons `v i ≤ v j`.

* `rank v i` — the number of blocks of `v` whose value is `< v i`; this is the
  canonical form of an ordered pattern.
* `rank_lt_iff`, `rank_eq_iff` — `rank` records the weak order faithfully.
* `rank_congr`, `rank_comp_strictMono` — ordered patterns are invariant under
  strictly monotone reparametrisation of the values, i.e. they are the
  invariants of the action of the order-automorphisms of the value line.
* `face_eq_iff` — two tuples span the same face iff they have the same ordered
  pattern; `face_convex`; a chamber is the face of an injective tuple
  (`face_eq_chamber`).
* `card_ordPatterns_le_four` — the face counts `1, 1, 3, 13, 75`, the
  ordered Bell (Fubini) numbers OEIS A000670.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X : Type*} [LinearOrder X]

/-! ### The ordered pattern (rank function) -/









/-! ### Faces of the braid arrangement -/






/-! ### Counting ordered patterns: the Fubini numbers -/











open Geometry.KernelPatterns in
theorem solution{v : Fin n → X} {i j : Fin n} : rank v i = rank v j ↔ v i = v j := by
  constructor
  · intro h
    rcases lt_trichotomy (v i) (v j) with hlt | heq | hgt
    · exact absurd (rank_lt_iff.2 hlt) (by rw [h]; exact lt_irrefl _)
    · exact heq
    · exact absurd (rank_lt_iff.2 hgt) (by rw [h]; exact lt_irrefl _)
  · intro h
    rcases lt_trichotomy (rank v i) (rank v j) with hlt | heq | hgt
    · exact absurd (rank_lt_iff.1 hlt) (by rw [h]; exact lt_irrefl _)
    · exact heq
    · exact absurd (rank_lt_iff.1 hgt) (by rw [h]; exact lt_irrefl _)
