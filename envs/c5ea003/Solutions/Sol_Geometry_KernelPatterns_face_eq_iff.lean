-- Prove2me | solution 1 for Geometry.KernelPatterns.face_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:40.958985+00:00
-- url     : https://prove2.me/submissions/09d12ac0-9f92-466d-84f0-f37d4a3a6f12

-- Sol generated from Geometry/KernelPatterns/Faces.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Definitions.Def_Geometry_KernelPatterns_Faces
import Theorems.Thm_Geometry_KernelPatterns_rank_congr
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



theorem mem_face_self (v : Fin n → ℝ) : v ∈ face v := fun _ _ => Iff.rfl



/-! ### Counting ordered patterns: the Fubini numbers -/











open Geometry.KernelPatterns in
theorem solution(v w : Fin n → ℝ) : face v = face w ↔ rank v = rank w := by
  constructor
  · intro h
    have hw : w ∈ face v := by rw [h]; exact mem_face_self w
    exact rank_congr fun i j => hw i j
  · intro h
    have hiff : ∀ i j, v i < v j ↔ w i < w j := by
      intro i j
      rw [← rank_lt_iff (v := v), ← rank_lt_iff (v := w), h]
    ext u
    exact ⟨fun hu i j => (hiff i j).symm.trans (hu i j),
      fun hu i j => (hiff i j).trans (hu i j)⟩
