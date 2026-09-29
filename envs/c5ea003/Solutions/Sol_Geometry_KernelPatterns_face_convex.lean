-- Prove2me | solution 1 for Geometry.KernelPatterns.face_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:39.58999+00:00
-- url     : https://prove2.me/submissions/89f8c624-d72e-436f-9d6a-100682cb61a2

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
theorem solution(v : Fin n → ℝ) : Convex ℝ (face v) := by
  intro w hw w' hw' a b ha hb hab i j
  constructor
  · intro hij
    have h1 : w i < w j := (hw i j).1 hij
    have h2 : w' i < w' j := (hw' i j).1 hij
    have key : a * w i + b * w' i < a * w j + b * w' j := by
      rcases eq_or_lt_of_le ha with ha0 | hapos
      · have hb1 : b = 1 := by linarith
        have ha1 : a = 0 := ha0.symm
        rw [ha1, hb1]; linarith
      · nlinarith [mul_lt_mul_of_pos_left h1 hapos, mul_le_mul_of_nonneg_left h2.le hb]
    simpa using key
  · intro hij
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · have h1 : w i = w j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have hv : v i < v j := (hw i j).2 h
          rw [heq] at hv; exact absurd hv (lt_irrefl _)
        · have hv : v j < v i := (hw j i).2 h
          rw [heq] at hv; exact absurd hv (lt_irrefl _)
      have h2 : w' i = w' j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have hv : v i < v j := (hw' i j).2 h
          rw [heq] at hv; exact absurd hv (lt_irrefl _)
        · have hv : v j < v i := (hw' j i).2 h
          rw [heq] at hv; exact absurd hv (lt_irrefl _)
      have : (a • w + b • w') i = (a • w + b • w') j := by
        simp [h1, h2]
      exact absurd hij (by rw [this]; exact lt_irrefl _)
    · have h1 : w j < w i := (hw j i).1 hlt
      have h2 : w' j < w' i := (hw' j i).1 hlt
      have key : a * w j + b * w' j < a * w i + b * w' i := by
        rcases eq_or_lt_of_le ha with ha0 | hapos
        · have hb1 : b = 1 := by linarith
          have ha1 : a = 0 := ha0.symm
          rw [ha1, hb1]; linarith
        · nlinarith [mul_lt_mul_of_pos_left h1 hapos, mul_le_mul_of_nonneg_left h2.le hb]
      have hlt' : (a • w + b • w') j < (a • w + b • w') i := by simpa using key
      exact absurd hij (not_lt.2 hlt'.le)
