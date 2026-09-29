-- Prove2me | solution 1 for Geometry.KernelPatterns.rank_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:57:06.952849+00:00
-- url     : https://prove2.me/submissions/4a734b4e-18ce-4cca-9100-196c97255307

-- Sol generated from Geometry/KernelPatterns/Faces.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Theorems.Thm_Geometry_KernelPatterns_rank_val

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
theorem solution{Y : Type*} [LinearOrder Y] {v : Fin n → X} {u : Fin n → Y}
    (h : ∀ i j, v i < v j ↔ u i < u j) : rank v = rank u := by
  have heq : ∀ i j, v i = v j ↔ u i = u j := by
    intro i j
    constructor
    · intro hij
      rcases lt_trichotomy (u i) (u j) with hlt | h' | hgt
      · exact absurd ((h i j).2 hlt) (by rw [hij]; exact lt_irrefl _)
      · exact h'
      · exact absurd ((h j i).2 hgt) (by rw [hij]; exact lt_irrefl _)
    · intro hij
      rcases lt_trichotomy (v i) (v j) with hlt | h' | hgt
      · exact absurd ((h i j).1 hlt) (by rw [hij]; exact lt_irrefl _)
      · exact h'
      · exact absurd ((h j i).1 hgt) (by rw [hij]; exact lt_irrefl _)
  have hpat : pat v = pat u := pat_congr heq
  funext i
  apply Fin.ext
  rw [rank_val, rank_val]
  refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
  rw [hpat]
  exact and_congr Iff.rfl (h k i)
