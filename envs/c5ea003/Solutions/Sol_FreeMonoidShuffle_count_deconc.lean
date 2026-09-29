-- Prove2me | solution 1 for FreeMonoidShuffle.count_deconc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:57:14.252691+00:00
-- url     : https://prove2.me/submissions/127a07ee-796a-4a6b-93f2-6ad6727dd43c

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_DeconcatenationShuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **Deconcatenation counts each split once**: `(z1, z2)` occurs in `deconc z` exactly once
if `z1 ++ z2 = z`, and not at all otherwise. -/
theorem solution {X : Type*} [DecidableEq X] (z1 z2 z : List X) :
    Multiset.count (z1, z2) (deconc z) = if z1 ++ z2 = z then 1 else 0 := by
  have hmem : ∀ (w : List X) (p : List X × List X), p ∈ deconc w ↔ p.1 ++ p.2 = w := by
    intro w
    induction w with
    | nil => intro p; simp [deconc, Prod.ext_iff]
    | cons a w ih =>
        rintro ⟨_ | ⟨b, p1⟩, p2⟩
        · simp [deconc]
        · simp [deconc, ih, eq_comm]
          exact and_comm
  have hnd : ∀ w : List X, (deconc w).Nodup := by
    intro w
    induction w with
    | nil => simp [deconc]
    | cons a w ih =>
        simp only [deconc]
        refine Multiset.nodup_cons.mpr ⟨?_, ih.map ?_⟩
        · simp
        · intro x y h
          simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
          exact Prod.ext_iff.mpr h
  by_cases h : z1 ++ z2 = z
  · rw [if_pos h]
    exact Multiset.count_eq_one_of_mem (hnd z) ((hmem z (z1, z2)).mpr h)
  · rw [if_neg h, Multiset.count_eq_zero]
    exact fun hm => h ((hmem z (z1, z2)).mp hm)
