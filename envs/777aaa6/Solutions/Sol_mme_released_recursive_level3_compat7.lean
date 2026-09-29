-- Prove2me | solution 1 for mme_released_recursive_level3_compat7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:12:59.480136+00:00
-- url     : https://prove2.me/submissions/35270da4-4f35-4ff3-af7a-3914bb452283

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3C

theorem hW : ∀ g : CompleteSplit.CompleteWord 2 → ℚ,
    ∑ v, g v = g ![0,0] + g ![0,1] + g ![0,2] + g ![1,0] + g ![1,1] + g ![1,2] + g ![2,0] + g ![2,1] + g ![2,2] := by
  have hu : (Finset.univ : Finset (CompleteSplit.CompleteWord 2)) = {![0,0], ![0,1], ![0,2], ![1,0], ![1,1], ![1,2], ![2,0], ![2,1], ![2,2]} := by
    decide +kernel
  intro g
  rw [hu]
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hpc {C W G : Type} [Fintype C] (B : C → Prop) (gp : C → G) (mu : C → W → ℕ)
    (g : G) (w : W) :
    partCount B gp mu (Sum.inr g) w = ∑ c, if ¬ B c ∧ gp c = g then mu c w else 0 := rfl

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 0 1 ⟨rr, c⟩ w else 0 := by
  rw [hpc, hcell]
  rw [Finset.sum_eq_single rr]
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val
    · rw [if_pos h, if_pos]
      refine ⟨h.1, ?_⟩
      simp [modeGroup, yzMode, Prod.ext_iff, Fin.ext_iff, h.2]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h2⟩
      exact h ⟨h1, by simpa [modeGroup, yzMode, Prod.ext_iff, Fin.ext_iff] using h2⟩
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hb (congrArg Prod.fst h)
  · intro h
    exact absurd (Finset.mem_univ rr) h

theorem hgrp2 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 0 2 ⟨rr, c⟩ w else 0 := by
  rw [hpc, hcell]
  rw [Finset.sum_eq_single rr]
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val
    · rw [if_pos h, if_pos]
      refine ⟨h.1, ?_⟩
      simp [modeGroup, yzMode, Prod.ext_iff, Fin.ext_iff, h.2]
    · rw [if_neg h, if_neg]
      rintro ⟨h1, h2⟩
      exact h ⟨h1, by simpa [modeGroup, yzMode, Prod.ext_iff, Fin.ext_iff] using h2⟩
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hb (congrArg Prod.fst h)
  · intro h
    exact absurd (Finset.mem_univ rr) h


theorem cp_0_46_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 25757454141812594476464851268140000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25757454141812594476464851268140000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) x = 25757454141812594476464851268140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_46_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 12878727070906297238232425634070000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12878727070906297238232425634070000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (46 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25757454141812594476464851268140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_46_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 42248132246016688091767574365930000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42248132246016688091767574365930000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42248132246016688091767574365930000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42248132246016688091767574365930000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 84496264492033376183535148731860000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_46_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 84496264492033376183535148731860000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (46 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84496264492033376183535148731860000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_46_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 25757454141812594476464851268140000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25757454141812594476464851268140000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 25757454141812594476464851268140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 110646349088841100955000000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (47 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 110646349088841100955000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 55323174544420550477500000000000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 55323174544420550477500000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (47 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 110646349088841100955000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 25942896862522064876654121101225000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25942896862522064876654121101225000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 25942896862522064876654121101225000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42351726113159518039172939449387500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42351726113159518039172939449387500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42351726113159518039172939449387500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42351726113159518039172939449387500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84703452226319036078345878898775000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42351726113159518039172939449387500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42351726113159518039172939449387500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42351726113159518039172939449387500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42351726113159518039172939449387500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 84703452226319036078345878898775000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_47_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (179531375866933652873901317681 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 465543792273845684292651276536286335752700000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25011809277974373508068818548152427328494600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 465543792273845684292651276536286335752700000000000000 else 0 := by
    intro v
    rw [hgrp2 (47 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25942896862522064876654121101225000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((4486235623 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((120513764377 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4486235623 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 1301462446109990460736845828049328000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (48 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1301462446109990460736845828049328000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 2259762406330782596699154171950672000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2259762406330782596699154171950672000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (48 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4519524812661565193398308343901344000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (407644728922106686630767991287 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 68081909199285357475824023318437614913643888000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1165298627711419745785197781412452770172712224000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 68081909199285357475824023318437614913643888000000000000 else 0 := by
    intro v
    rw [hgrp1 (48 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1301462446109990460736845828049328000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((4779388554518240136977 : ℚ)/91363400237000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((40902311563981759863023 : ℚ)/45681700118500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4779388554518240136977 : ℚ)/91363400237000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 50352354914282163939832069822076000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 50352354914282163939832069822076000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 50352354914282163939832069822076000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 1129881203165391298349577085975336000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1129881203165391298349577085975336000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1129881203165391298349577085975336000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1129881203165391298349577085975336000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2259762406330782596699154171950672000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (414751644479008205844653918488 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 67020663512019407163199901706492235353741084000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1117068764171669482470613954814267529292517832000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 67020663512019407163199901706492235353741084000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 67020663512019407163199901706492235353741084000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1117068764171669482470613954814267529292517832000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 67020663512019407163199901706492235353741084000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 1251110091195708296797013758227252000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((53568957667 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446431042333 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53568957667 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 625555045597854148398506879113626000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 625555045597854148398506879113626000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 625555045597854148398506879113626000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 625555045597854148398506879113626000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 1251110091195708296797013758227252000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 2259762406330782596699154171950672000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (48 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2259762406330782596699154171950672000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_48_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 25176177457141081969916034911038000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25176177457141081969916034911038000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (48 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 50352354914282163939832069822076000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 236794747427779458936120824432480000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (49 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 236794747427779458936120824432480000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 4452560983195777333291939587783760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4452560983195777333291939587783760000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (49 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 8905121966391554666583879175567520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (359369415617705843815945384852 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 392540161208615518028872951814414399965995680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8120041643974323630526133271938691200068008640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 392540161208615518028872951814414399965995680000000000000 else 0 := by
    intro v
    rw [hgrp1 (49 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 8905121966391554666583879175567520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((21469248380661469188217 : ℚ)/487048955113000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((222055229175838530811783 : ℚ)/243524477556500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21469248380661469188217 : ℚ)/487048955113000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 115375889443712522804301050870480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 115375889443712522804301050870480000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (49 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 230751778887425045608602101740960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 3021484270177206663759361345760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 3021484270177206663759361345760000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 3021484270177206663759361345760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 3021484270177206663759361345760000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 6042968540354413327518722691520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 6042968540354413327518722691520000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 6042968540354413327518722691520000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 6042968540354413327518722691520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 595465700014033033745290535348320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 595465700014033033745290535348320000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 595465700014033033745290535348320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 595465700014033033745290535348320000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 1190931400028066067490581070696640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (380580251575718374753858120965 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 367439392129486548120010088658363582356294880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6979311782104515502853277927554152835287410240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 367439392129486548120010088658363582356294880000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 367439392129486548120010088658363582356294880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6979311782104515502853277927554152835287410240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 367439392129486548120010088658363582356294880000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 7714190566363488599093298104870880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((47631619801 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((452368380199 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((47631619801 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 115375889443712522804301050870480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 115375889443712522804301050870480000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 115375889443712522804301050870480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 115375889443712522804301050870480000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 230751778887425045608602101740960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 115375889443712522804301050870480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 115375889443712522804301050870480000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 115375889443712522804301050870480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 115375889443712522804301050870480000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 230751778887425045608602101740960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (10396861359573246658583164103 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 4782404380287902907162304107618182465930400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7704625757602912793278973496655643635068139200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 4782404380287902907162304107618182465930400000000000000 else 0 := by
    intro v
    rw [hgrp2 (49 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7714190566363488599093298104870880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((123989791 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((99876010209 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((123989791 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 595465700014033033745290535348320000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 595465700014033033745290535348320000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (49 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1190931400028066067490581070696640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_49_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 6042968540354413327518722691520000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (49 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6042968540354413327518722691520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (247850527569049974470444790873 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 27195922554902364678096221449640799803959702000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 951335497916422838061638801069827400392080596000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 27195922554902364678096221449640799803959702000000000000 else 0 := by
    intro v
    rw [hgrp1 (50 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1005727343026227567417831243969109000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((13322347665744863019541 : ℚ)/492671255909500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((233013280289005136980459 : ℚ)/246335627954750000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13322347665744863019541 : ℚ)/492671255909500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 322198320131334049196219580517667500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 322198320131334049196219580517667500000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (50 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 644396640262668098392439161035335000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 14960723268198291493168756030891000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 14960723268198291493168756030891000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 14960723268198291493168756030891000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 7480361634099145746584378015445500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7480361634099145746584378015445500000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (50 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 14960723268198291493168756030891000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 180665351381779734512696041466887000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 180665351381779734512696041466887000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 180665351381779734512696041466887000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 180665351381779734512696041466887000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 361330702763559469025392082933774000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319511101926457447950130718234 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 13614239135437115250869265842675633642309312000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 334102224492685238523653551248422732715381376000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13614239135437115250869265842675633642309312000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 13614239135437115250869265842675633642309312000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 334102224492685238523653551248422732715381376000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13614239135437115250869265842675633642309312000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 361330702763559469025392082933774000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1177439309 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 4 then ((14447560691 : ℚ)/15625000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1177439309 : ℚ)/31250000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 322198320131334049196219580517667500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 322198320131334049196219580517667500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 322198320131334049196219580517667500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 322198320131334049196219580517667500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 644396640262668098392439161035335000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 14960723268198291493168756030891000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 14960723268198291493168756030891000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 14960723268198291493168756030891000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 14960723268198291493168756030891000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (50 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 14960723268198291493168756030891000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 322198320131334049196219580517667500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 322198320131334049196219580517667500000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (50 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 644396640262668098392439161035335000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_50_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 361330702763559469025392082933774000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (50 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 361330702763559469025392082933774000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 42285394528715369217598041626700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42285394528715369217598041626700000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (51 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84570789057430738435196083253400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 26301885798817404104803916746600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 26301885798817404104803916746600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 26301885798817404104803916746600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (203941699295310938384108077146 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 554338984942311822536296193987241353391800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25193207828932780459731324358625517293216400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 554338984942311822536296193987241353391800000000000000 else 0 := by
    intro v
    rw [hgrp1 (51 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 26301885798817404104803916746600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((21076016723 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((478923983277 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21076016723 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42285394528715369217598041626700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42285394528715369217598041626700000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42285394528715369217598041626700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42285394528715369217598041626700000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 84570789057430738435196083253400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 42285394528715369217598041626700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42285394528715369217598041626700000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42285394528715369217598041626700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42285394528715369217598041626700000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84570789057430738435196083253400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 26301885798817404104803916746600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26301885798817404104803916746600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 26301885798817404104803916746600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 13150942899408702052401958373300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 13150942899408702052401958373300000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (51 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 26301885798817404104803916746600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_51_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 84570789057430738435196083253400000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (51 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84570789057430738435196083253400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 3190272719450719236191000000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (52 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3190272719450719236191000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 1595136359725359618095500000000000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1595136359725359618095500000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (52 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3190272719450719236191000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 45104244211418764509356975136238000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 45104244211418764509356975136238000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 45104244211418764509356975136238000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 559390117490323870932912293206930000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 559390117490323870932912293206930000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 559390117490323870932912293206930000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 559390117490323870932912293206930000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 1118780234980647741865824586413860000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 1013194120129326364907909219224951000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1013194120129326364907909219224951000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1013194120129326364907909219224951000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1013194120129326364907909219224951000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 2026388240258652729815818438449902000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 2026388240258652729815818438449902000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (52 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2026388240258652729815818438449902000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (414845728425819450195646552378 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 59950598485040988888703254780857984617419280000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 998879038010565764088418076852144030765161440000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 59950598485040988888703254780857984617419280000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 59950598485040988888703254780857984617419280000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 998879038010565764088418076852144030765161440000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 59950598485040988888703254780857984617419280000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 1118780234980647741865824586413860000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((13396419737 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((111603580263 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((13396419737 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_52_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 22552122105709382254678487568119000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22552122105709382254678487568119000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (52 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 45104244211418764509356975136238000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 3901781857810744566685533665887008000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (53 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3901781857810744566685533665887008000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 6714308609610855655746466334112992000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 6714308609610855655746466334112992000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (53 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 13428617219221711311492932668225984000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371157594210571881397562203042 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 179317741085980311453011430442911113649102496000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 3536066910578725510172780203995201772701795008000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 179317741085980311453011430442911113649102496000000000000 else 0 := by
    intro v
    rw [hgrp1 (53 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3894702392750686133078803064881024000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((16891127824905620993603 : ℚ)/366867860132000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((166542802241094379006397 : ℚ)/183433930066000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((16891127824905620993603 : ℚ)/366867860132000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (283655225976475671476557958334 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 228074466497052743110019936471465040636384000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6623316127064328120510561133041069918727232000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 228074466497052743110019936471465040636384000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 228074466497052743110019936471465040636384000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6623316127064328120510561133041069918727232000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 228074466497052743110019936471465040636384000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 7079465060058433606730601005984000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((32216341851 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((467783658149 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((32216341851 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 7079465060058433606730601005984000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7079465060058433606730601005984000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 7079465060058433606730601005984000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 409855726879399451266709774922416000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 409855726879399451266709774922416000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 409855726879399451266709774922416000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 409855726879399451266709774922416000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 819711453758798902533419549844832000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (410215198900365192610125367917 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 161883841492299073778322931774090875978315776000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2744238262718861268210923255722762248043368448000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 161883841492299073778322931774090875978315776000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 161883841492299073778322931774090875978315776000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2744238262718861268210923255722762248043368448000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 161883841492299073778322931774090875978315776000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 3068005945703459415767569119270944000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((824455711 : ℚ)/15625000000) else if 3 * (v 0).val + (v 1).val = 4 then ((6988044289 : ℚ)/7812500000) else if 3 * (v 0).val + (v 1).val = 6 then ((824455711 : ℚ)/15625000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 413348223523613358655616972805040000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 413348223523613358655616972805040000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 413348223523613358655616972805040000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 413348223523613358655616972805040000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 826696447047226717311233945610080000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (53267539441704540028226035297 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 48365502201570075898042724625741540503978240000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11692463307300973354630008119284836918992043520000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 48365502201570075898042724625741540503978240000000000000 else 0 := by
    intro v
    rw [hgrp2 (53 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11789194311704113506426093568536320000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((4102528207 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((495897471793 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4102528207 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 823203950403012809922326747727456000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 823203950403012809922326747727456000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (53 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1646407900806025619844653495454912000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (409855693792053264384684342165 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 161689044195015757033891336873984589544972000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2744627857313427901699786445522974820910056000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 161689044195015757033891336873984589544972000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 161689044195015757033891336873984589544972000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2744627857313427901699786445522974820910056000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 161689044195015757033891336873984589544972000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 3068005945703459415767569119270944000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((421613379 : ℚ)/8000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((3578386621 : ℚ)/4000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((421613379 : ℚ)/8000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_53_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 7079465060058433606730601005984000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (53 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7079465060058433606730601005984000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (210233498966235407095509154464 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 248490347606095134663462622908291393360986352000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10847177766735853426070940394683335213278027296000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 248490347606095134663462622908291393360986352000000000000 else 0 := by
    intro v
    rw [hgrp1 (54 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11344158461948043695397865640499918000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((3821700178949518118253 : ℚ)/174469442542625000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((83413021092362981881747 : ℚ)/87234721271312500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((3821700178949518118253 : ℚ)/174469442542625000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 302472686665907671427692650901362000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 302472686665907671427692650901362000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (54 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 604945373331815342855385301802724000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 5457872328336878237390919047772000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 5457872328336878237390919047772000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 5457872328336878237390919047772000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 643593560121723876938213901352002000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 643593560121723876938213901352002000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (54 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1287187120243447753876427802704004000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 341120873455816205510521250450640000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 341120873455816205510521250450640000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 341120873455816205510521250450640000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 341120873455816205510521250450640000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 682241746911632411021042500901280000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 5457872328336878237390919047772000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (54 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 5457872328336878237390919047772000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (377643051931161653650639780571 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 109622522671681709478545525569303939246228050000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2106529050585025894613405864857922121507543900000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 109622522671681709478545525569303939246228050000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 1 ⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 109622522671681709478545525569303939246228050000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2106529050585025894613405864857922121507543900000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 109622522671681709478545525569303939246228050000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2325774095928389313570496915996530000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((9426755837 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((90573244163 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9426755837 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_0_54_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (323300079075674405169197012207 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 89011088247239265232557345377599931583402420000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2147751919433910783105382225241330136833195160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 89011088247239265232557345377599931583402420000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 0 2 ⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 89011088247239265232557345377599931583402420000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2147751919433910783105382225241330136833195160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 89011088247239265232557345377599931583402420000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2325774095928389313570496915996530000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((19135798357 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((230864201643 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((19135798357 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


end L3C

theorem solution :
    (regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (179531375866933652873901317681 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (407644728922106686630767991287 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (414751644479008205844653918488 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then 0 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (359369415617705843815945384852 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (380580251575718374753858120965 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (10396861359573246658583164103 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (247850527569049974470444790873 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319511101926457447950130718234 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (203941699295310938384108077146 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (414845728425819450195646552378 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371157594210571881397562203042 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -6 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (283655225976475671476557958334 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (410215198900365192610125367917 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (53267539441704540028226035297 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (409855693792053264384684342165 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 1 else if k.val = 2 then 4 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (210233498966235407095509154464 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (377643051931161653650639780571 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inl ⟨⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (323300079075674405169197012207 : ℚ)/10^30) :=
  ⟨L3C.cp_0_46_1_3, L3C.cp_0_46_2_0, L3C.cp_0_46_2_1, L3C.cp_0_46_2_2, L3C.cp_0_46_2_3, L3C.cp_0_47_1_0, L3C.cp_0_47_1_1, L3C.cp_0_47_2_0, L3C.cp_0_47_2_1, L3C.cp_0_47_2_2, L3C.cp_0_47_2_3, L3C.cp_0_48_1_0, L3C.cp_0_48_1_1, L3C.cp_0_48_1_2, L3C.cp_0_48_2_0, L3C.cp_0_48_2_1, L3C.cp_0_48_2_2, L3C.cp_0_48_2_3, L3C.cp_0_48_2_4, L3C.cp_0_48_2_5, L3C.cp_0_49_1_0, L3C.cp_0_49_1_1, L3C.cp_0_49_1_2, L3C.cp_0_49_1_3, L3C.cp_0_49_1_4, L3C.cp_0_49_2_0, L3C.cp_0_49_2_1, L3C.cp_0_49_2_2, L3C.cp_0_49_2_3, L3C.cp_0_49_2_4, L3C.cp_0_49_2_5, L3C.cp_0_49_2_6, L3C.cp_0_49_2_7, L3C.cp_0_50_1_0, L3C.cp_0_50_1_1, L3C.cp_0_50_1_2, L3C.cp_0_50_1_3, L3C.cp_0_50_1_4, L3C.cp_0_50_2_0, L3C.cp_0_50_2_1, L3C.cp_0_50_2_2, L3C.cp_0_50_2_3, L3C.cp_0_50_2_4, L3C.cp_0_50_2_5, L3C.cp_0_51_1_0, L3C.cp_0_51_1_1, L3C.cp_0_51_1_2, L3C.cp_0_51_1_3, L3C.cp_0_51_2_0, L3C.cp_0_51_2_1, L3C.cp_0_51_2_2, L3C.cp_0_51_2_3, L3C.cp_0_52_1_0, L3C.cp_0_52_1_1, L3C.cp_0_52_2_0, L3C.cp_0_52_2_1, L3C.cp_0_52_2_2, L3C.cp_0_52_2_3, L3C.cp_0_52_2_4, L3C.cp_0_52_2_5, L3C.cp_0_53_1_0, L3C.cp_0_53_1_1, L3C.cp_0_53_1_2, L3C.cp_0_53_1_3, L3C.cp_0_53_2_0, L3C.cp_0_53_2_1, L3C.cp_0_53_2_2, L3C.cp_0_53_2_3, L3C.cp_0_53_2_4, L3C.cp_0_53_2_5, L3C.cp_0_53_2_6, L3C.cp_0_53_2_7, L3C.cp_0_54_1_0, L3C.cp_0_54_1_1, L3C.cp_0_54_1_2, L3C.cp_0_54_1_3, L3C.cp_0_54_1_4, L3C.cp_0_54_1_5, L3C.cp_0_54_1_6, L3C.cp_0_54_2_0⟩
