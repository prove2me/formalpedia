-- Prove2me | solution 1 for davenport_constant_groups
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:39.258466+00:00
-- url     : https://prove2.me/submissions/d8ae8639-bf2c-4ace-8d4c-78070f18a338

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

private theorem zero_sum_of_card_le (n D : ℕ) [NeZero n] (hD : n ≤ D)
    (seq : Fin D → ZMod n) : ∃ I : Finset (Fin D), I.Nonempty ∧ I.sum seq = 0 := by
  classical
  let initialSegment (k : Fin (D + 1)) : Finset (Fin D) := Finset.univ.filter (fun i => i.val < k.val)
  let f (k : Fin (D + 1)) : ZMod n := (initialSegment k).sum seq
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (D + 1)) := by
    simp only [ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hsum⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have ordered (i j : Fin (D + 1)) (hij : i < j) (hsum : f i = f j) :
      ∃ I : Finset (Fin D), I.Nonempty ∧ I.sum seq = 0 := by
    have hsub : initialSegment i ⊆ initialSegment j := by
      intro a ha
      simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact lt_trans ha hij
    have hiD : i.val < D := by have := j.isLt; omega
    refine ⟨initialSegment j \ initialSegment i, ?_, ?_⟩
    · refine ⟨⟨i.val, hiD⟩, ?_⟩
      simp only [Finset.mem_sdiff, initialSegment, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, lt_irrefl _⟩
    · rw [Finset.sum_sdiff_eq_sub hsub]
      change f j - f i = 0
      rw [hsum, sub_self]
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h hsum
  · exact ordered j i h hsum.symm

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (D : ℕ), D = 2 * n - 1 ∧
    ∀ (seq : Fin D → ZMod n),
      ∃ (I : Finset (Fin D)) (_ : I.Nonempty), (I.sum seq) = 0 := by
  letI : NeZero n := ⟨by omega⟩
  refine ⟨2 * n - 1, rfl, ?_⟩
  intro seq
  obtain ⟨I, hI, hsum⟩ := zero_sum_of_card_le n (2 * n - 1) (by omega) seq
  exact ⟨I, hI, hsum⟩

#print axioms solution
