-- Prove2me | solution 1 for Geometry.KernelPatterns.rank_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:57:07.438356+00:00
-- url     : https://prove2.me/submissions/1fc12731-3fc4-41a3-bcb1-2fb9198bb332

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
theorem solution{v : Fin n → X} {i j : Fin n} : rank v i < rank v j ↔ v i < v j := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have hsub : (univ.filter fun k => pat v k = k ∧ v k < v j) ⊆
        (univ.filter fun k => pat v k = k ∧ v k < v i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hk.1, lt_of_lt_of_le hk.2 hle⟩
    have := Finset.card_le_card hsub
    rw [Fin.lt_def, rank_val, rank_val] at h
    omega
  · intro h
    have hsub : (univ.filter fun k => pat v k = k ∧ v k < v i) ⊂
        (univ.filter fun k => pat v k = k ∧ v k < v j) := by
      refine ⟨fun k hk => ?_, fun hcon => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact ⟨hk.1, hk.2.trans h⟩
      · have hmem : pat v i ∈ (univ.filter fun k => pat v k = k ∧ v k < v j) := by
          simp [apply_pat, h]
        have := hcon hmem
        simp [apply_pat] at this
    rw [Fin.lt_def, rank_val, rank_val]
    exact Finset.card_lt_card hsub
