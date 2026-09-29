-- Prove2me | solution 1 for mme_released_global_two_part_split_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T20:30:33.2834+00:00
-- url     : https://prove2.me/submissions/3bd04414-11c5-4f67-afbf-2fcf9dc9e7fd

import Mathlib
import Definitions.Def_mme_released_global_two_part_split_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace MME.ReleasedRecursive.Asm

variable {k : ℕ}

/-- Splitting a part word by its own blocks. -/
theorem split_refl {L N ell : ℕ} (h : L * 2 ^ (ell - 1) = N) (y : FineWord N) (p : Fin L) :
    split (Equiv.refl (Fin L)) h y p = fun r ↦ y (Fin.cast h (finProdFinEquiv (p, r))) := rfl

/-- The boundary part fixes the grades of its blocks. -/
theorem zero_grade (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h0 : QZero k a i (fun r ↦ x (partPositions k a ⟨0, r⟩)))
    (b : Blk k) (hb : isZeroCell (cellOf k a b)) :
    CWCells.grade (blockWord k x b) = ((cellOf k a b).val (hashMode b.1 i)).val := by
  have hq := h0.1 (zEnum k a ⟨b, hb⟩)
  simp only [zCellOf_apply, Equiv.symm_apply_apply, zGradeAt_idx, split_refl] at hq
  rw [show (fun r ↦ (fun t ↦ x (partPositions k a ⟨0, t⟩))
      (Fin.cast (zLen k a) (finProdFinEquiv (zEnum k a ⟨b, hb⟩, r)))) =
      blockWord k x b from by
    rw [zWord k a x (zEnum k a ⟨b, hb⟩), Equiv.symm_apply_apply]] at hq
  exact hq

/-- The hashed part fixes the grades of its blocks. -/
theorem pos_grade (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h1 : QPos k a eps i (fun r ↦ x (partPositions k a ⟨1, r⟩)))
    (b : Blk k) (hb : ¬ isZeroCell (cellOf k a b)) :
    CWCells.grade (blockWord k x b) = ((cellOf k a b).val (hashMode b.1 i)).val := by
  have hq := h1.1 ⟨b, hb⟩
  rw [pWord k a x ⟨b, hb⟩] at hq
  exact hq

/-- The boundary part fixes the histograms of its cells. -/
theorem zero_count (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h0 : QZero k a i (fun r ↦ x (partPositions k a ⟨0, r⟩))) (C : ZCell) (w : Word) :
    Fintype.card {b : Fin (blocks k) // (a C.val.1).val 0 b = C.val.2 ∧
        blockWord k x ⟨C.val.1, b⟩ = w} =
      scaledWords C.val.1 k (hashMode C.val.1 i) (cellOfShape C.val.2) w := by
  classical
  have hu := h0.2 (zCellIdx C) w
  rw [zMu_eq k hk a C i w] at hu
  rw [← hu, ← zCount_eq k a C x w, Fintype.card_subtype]
  unfold count
  refine (Finset.card_nbij (i := fun q ↦ q) ?_ ?_ ?_).symm
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨zCellIdx.injective ?_, ?_⟩
    · rw [← zCellOf_apply k a q]
      exact hq.1
    · rw [← hq.2, split_refl, zWord k a x q]
  · intro q hq r hr hqr
    exact hqr
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨q, ⟨?_, ?_⟩, rfl⟩
    · rw [zCellOf_apply k a q, hq.1]
    · rw [split_refl, zWord k a x q]
      exact hq.2

/-- The hashed part keeps its cell histograms inside the window. -/
theorem pos_count (k : ℕ) (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h1 : QPos k a eps i (fun r ↦ x (partPositions k a ⟨1, r⟩))) (o : Fin 6) (c : Shape)
    (hc : ¬ isZeroCell c) (w : Word) :
    |(Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c ∧ blockWord k x ⟨o, b⟩ = w} : ℝ) /
        (blocks k : ℝ) - (profile o).2 (hashMode o i) (cellOfShape c) w| ≤ eps o := by
  have h := h1.2 o c hc w
  rw [show Fintype.card {b : PBlk k a // b.val.1 = o ∧ (a o).val 0 b.val.2 = c ∧
      pBlockWord k a (fun r ↦ x (partPositions k a ⟨1, r⟩)) b = w} =
      Fintype.card {b : Fin (blocks k) // (a o).val 0 b = c ∧ blockWord k x ⟨o, b⟩ = w} from by
    rw [← pCount_eq k a o c hc x w]
    refine Fintype.card_congr (Equiv.subtypeEquivRight (fun b ↦ ?_))
    rw [pWord k a x b]] at h
  exact h

/-- Scaling cancels in the frequency. -/
theorem div_scale (N D k : ℕ) (hk : 0 < k) (hD : 0 < D) :
    ((k * N : ℕ) : ℝ) / ((D * k : ℕ) : ℝ) = (N : ℝ) / (D : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact this.ne'
  have hD' : (D : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    exact this.ne'
  push_cast
  field_simp

/-- The released profile is the scaled histogram divided by the block count. -/
theorem profile_eq (o : Fin 6) (k : ℕ) (hk : 0 < k) (c : Shape) (j : Fin 3) (w : Word) :
    (scaledWords o k j (cellOfShape c) w : ℝ) / (blocks k : ℝ) =
      (profile o).2 j (cellOfShape c) w := by
  have hD : 0 < MoreAsymmetryExactSeed.denominator ^ 5 := by
    have : 0 < MoreAsymmetryExactSeed.denominator := by
      unfold MoreAsymmetryExactSeed.denominator
      omega
    positivity
  show ((k * wordCounts o j c w : ℕ) : ℝ) /
      ((MoreAsymmetryExactSeed.denominator ^ 5 * k : ℕ) : ℝ) =
    (wordCounts o j c w : ℝ) / ((MoreAsymmetryExactSeed.denominator : ℝ) ^ 5)
  rw [div_scale (wordCounts o j c w) (MoreAsymmetryExactSeed.denominator ^ 5) k hk hD]
  push_cast
  ring

/-- The two parts together give the joint window. -/
theorem partition_inside (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (heps : ∀ o, 0 ≤ eps o) (i : Fin 3) (x : FineWord (4 * (6 * blocks k)))
    (h0 : QZero k a i (fun r ↦ x (partPositions k a ⟨0, r⟩)))
    (h1 : QPos k a eps i (fun r ↦ x (partPositions k a ⟨1, r⟩))) :
    jointWindow k hk a eps i x := by
  intro o
  rw [window_iff k hk o a (eps o) i x]
  refine ⟨fun b ↦ ?_, fun c w ↦ ?_⟩
  · by_cases hb : isZeroCell (cellOf k a ⟨o, b⟩)
    · exact zero_grade k hk a i x h0 ⟨o, b⟩ hb
    · exact pos_grade k a eps i x h1 ⟨o, b⟩ hb
  · by_cases hc : isZeroCell c
    · rw [zero_count k hk a i x h0 ⟨(o, c), hc⟩ w, profile_eq o k hk c (hashMode o i) w, sub_self,
        abs_zero]
      exact heps o
    · exact pos_count k a eps i x h1 o c hc w

end MME.ReleasedRecursive.Asm

theorem solution (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o) (i : Fin 3)
    (x : FineWord (4 * (6 * blocks k)))
    (h0 : QZero k a i (fun r ↦ x (partPositions k a ⟨0, r⟩)))
    (h1 : QPos k a eps i (fun r ↦ x (partPositions k a ⟨1, r⟩))) :
    jointWindow k hk a eps i x :=
  MME.ReleasedRecursive.Asm.partition_inside k hk a eps heps i x h0 h1
