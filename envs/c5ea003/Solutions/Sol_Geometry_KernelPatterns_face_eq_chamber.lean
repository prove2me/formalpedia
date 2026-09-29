-- Prove2me | solution 1 for Geometry.KernelPatterns.face_eq_chamber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:40.410983+00:00
-- url     : https://prove2.me/submissions/77aa0ede-8908-4913-b5bb-d6a5babc61e1

-- Sol generated from Geometry/KernelPatterns/Faces.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Faces

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
theorem solution{σ : Equiv.Perm (Fin n)} {v : Fin n → ℝ} (hv : v ∈ chamber n σ) :
    face v = chamber n σ := by
  ext w
  constructor
  · intro hw i j hij
    exact (hw (σ i) (σ j)).1 (hv i j hij)
  · intro hw i j
    constructor
    · intro hij
      have hlt : σ.symm i < σ.symm j := by
        by_contra hle
        push_neg at hle
        rcases eq_or_lt_of_le hle with heq | hlt'
        · have : i = j := by
            have := congrArg σ heq
            simpa using this.symm
          exact absurd hij (by rw [this]; exact lt_irrefl _)
        · have := hv _ _ hlt'
          simp only [Equiv.apply_symm_apply] at this
          exact absurd hij (not_lt.2 this.le)
      have := hw _ _ hlt
      simpa using this
    · intro hij
      have hlt : σ.symm i < σ.symm j := by
        by_contra hle
        push_neg at hle
        rcases eq_or_lt_of_le hle with heq | hlt'
        · have : i = j := by
            have := congrArg σ heq
            simpa using this.symm
          exact absurd hij (by rw [this]; exact lt_irrefl _)
        · have := hw _ _ hlt'
          simp only [Equiv.apply_symm_apply] at this
          exact absurd hij (not_lt.2 this.le)
      have := hv _ _ hlt
      simpa using this
