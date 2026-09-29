-- Prove2me | solution 1 for mme_released_recursive_level3_compat30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T10:33:36.920718+00:00
-- url     : https://prove2.me/submissions/e6871ea0-d3cd-4d94-899c-8ab2a6cdd06e

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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 2 1 ⟨rr, c⟩ w else 0 := by
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
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 2 2 ⟨rr, c⟩ w else 0 := by
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


theorem cp_2_38_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (4368716790414123879312362 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 283980640161024969634586552091401748000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2191787957828060730790936609846645817196504000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 283980640161024969634586552091401748000000000000000 else 0 := by
    intro v
    rw [hgrp1 (38 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2191788525789341052840875879019750000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((62873317045649 : ℚ)/485262005187500000000) else if 3 * (v 0).val + (v 1).val = 4 then ((242630939720432954351 : ℚ)/242631002593750000000) else if 3 * (v 0).val + (v 1).val = 6 then ((62873317045649 : ℚ)/485262005187500000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 16795521452360892538192470894081262500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 16795521452360892538192470894081262500000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (38 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 33591042904721785076384941788162525000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 10246980878504985453350613277401225000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (38 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 10246980878504985453350613277401225000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (340038785473895137666573645465 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 330486805781948919695416022626087295725989900000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7413181777245717239342904491232750408548020200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 330486805781948919695416022626087295725989900000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 330486805781948919695416022626087295725989900000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7413181777245717239342904491232750408548020200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 330486805781948919695416022626087295725989900000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 8074155388809615078733736536484925000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((10232859967 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((114767140033 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10232859967 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 1167982106246631155557916690414062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1167982106246631155557916690414062500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1167982106246631155557916690414062500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1167982106246631155557916690414062500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2335964212493262311115833380828125000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 18963036093970678223999138103450000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 18963036093970678223999138103450000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) x = 18963036093970678223999138103450000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (126853399990626014245543099 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 90777343268292026664403106042606184600000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18962854539284141639945809297237914787630800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 90777343268292026664403106042606184600000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 90777343268292026664403106042606184600000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 18962854539284141639945809297237914787630800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 90777343268292026664403106042606184600000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 18963036093970678223999138103450000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1196767 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((124998803233 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1196767 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 2335964212493262311115833380828125000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (38 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2335964212493262311115833380828125000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 16713952090961946569942992574125350000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 16713952090961946569942992574125350000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (38 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 33427904181923893139885985148250700000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (342174798412163354704642674823 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 333263227630820243849730092402859172333622550000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7407628933547974591034276351679206655332754900000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 333263227630820243849730092402859172333622550000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 333263227630820243849730092402859172333622550000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7407628933547974591034276351679206655332754900000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 333263227630820243849730092402859172333622550000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 8074155388809615078733736536484925000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((20637652583 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((229362347417 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20637652583 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 10410119601302877389849569917313050000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (38 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 10410119601302877389849569917313050000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 1086412744847685187308438370458150000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1086412744847685187308438370458150000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1086412744847685187308438370458150000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1086412744847685187308438370458150000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 2172825489695370374616876740916300000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_38_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 18963036093970678223999138103450000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 18963036093970678223999138103450000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 18963036093970678223999138103450000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 171963060939721776502382527804224000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (39 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 171963060939721776502382527804224000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 3352390804709600636432808736097888000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3352390804709600636432808736097888000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (39 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6704781609419201272865617472195776000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (351608687166216478644883091734 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 287005636175933597193628929185491245231723832000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6130770337067334078478359613824793509536552336000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 287005636175933597193628929185491245231723832000000000000 else 0 := by
    intro v
    rw [hgrp1 (39 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6704781609419201272865617472195776000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((41735683078800961001149 : ℚ)/974993537032000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((445761085437199038998851 : ℚ)/487496768516000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((41735683078800961001149 : ℚ)/974993537032000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 83737999906780065571818308923344000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83737999906780065571818308923344000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (39 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 167475999813560131143636617846688000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 2243530563080822679372954978768000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2243530563080822679372954978768000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2243530563080822679372954978768000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2243530563080822679372954978768000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 4487061126161645358745909957536000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 4487061126161645358745909957536000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4487061126161645358745909957536000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 4487061126161645358745909957536000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 422288649522145661869533389892268000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 422288649522145661869533389892268000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 422288649522145661869533389892268000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 422288649522145661869533389892268000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 844577299044291323739066779784536000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370611240648506903188358471147 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 269275587546097906328916133731218793239793520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5321653135282714136468718424948802413520412960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 269275587546097906328916133731218793239793520000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 269275587546097906328916133731218793239793520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5321653135282714136468718424948802413520412960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 269275587546097906328916133731218793239793520000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 5860204310374909949126550692411240000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((22974931699 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((227025068301 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((22974931699 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 83737999906780065571818308923344000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 83737999906780065571818308923344000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 83737999906780065571818308923344000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 83737999906780065571818308923344000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 167475999813560131143636617846688000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 83737999906780065571818308923344000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83737999906780065571818308923344000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 83737999906780065571818308923344000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83737999906780065571818308923344000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 167475999813560131143636617846688000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5070859287181971992510909971 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 1615739404296996709853336191726608377505400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5856972831566315955706844020027786783244989200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1615739404296996709853336191726608377505400000000000000 else 0 := by
    intro v
    rw [hgrp2 (39 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 5860204310374909949126550692411240000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((55142767 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((99944857233 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((55142767 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 422288649522145661869533389892268000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 422288649522145661869533389892268000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (39 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 844577299044291323739066779784536000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_39_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 4487061126161645358745909957536000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (39 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4487061126161645358745909957536000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (96354281358297841788661651403 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 192247929782992605054078627450151105924225632000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 22674887023814344849464434625296337788151548736000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 192247929782992605054078627450151105924225632000000000000 else 0 := by
    intro v
    rw [hgrp1 (40 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 23059382883380330059572591880196640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((449530161108686576401 : ℚ)/53919374395000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((26510157036391313423599 : ℚ)/26959687197500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((449530161108686576401 : ℚ)/53919374395000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 54280487122603715756424129877548000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 54280487122603715756424129877548000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (40 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 108560974245207431512848259755096000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 16966854965933193726228056480129448000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 16966854965933193726228056480129448000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (40 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 33933709931866387452456112960258896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 410502483603603352781282341082556000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 410502483603603352781282341082556000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 410502483603603352781282341082556000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 410502483603603352781282341082556000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 821004967207206705562564682165112000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 929565941452414137075412941920208000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (40 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 929565941452414137075412941920208000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (404234177990123790920497863946 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 602439666002376922512421570136948916193609680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10444850181757757680063152037609254167612780640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 602439666002376922512421570136948916193609680000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 602439666002376922512421570136948916193609680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10444850181757757680063152037609254167612780640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 602439666002376922512421570136948916193609680000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 11649729513762511525087995177883152000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((10342551993 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((89657448007 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10342551993 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 387701232638227066102237048910448000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 387701232638227066102237048910448000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 387701232638227066102237048910448000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 387701232638227066102237048910448000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 775402465276454132204474097820896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (251291806442747958114693906966 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 21344014949528565571723108109030644713698976000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 732714435377397001061027881602834710572602048000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 21344014949528565571723108109030644713698976000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 21344014949528565571723108109030644713698976000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 732714435377397001061027881602834710572602048000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 21344014949528565571723108109030644713698976000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 775402465276454132204474097820896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((27526369731 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((472473630269 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((27526369731 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 54280487122603715756424129877548000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54280487122603715756424129877548000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 54280487122603715756424129877548000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54280487122603715756424129877548000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 108560974245207431512848259755096000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (181069906593781779461964407231 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 211306363863736631426077804501686921489098880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11227116786035038262235839568879778157021802240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 211306363863736631426077804501686921489098880000000000000 else 0 := by
    intro v
    rw [hgrp2 (40 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11649729513762511525087995177883152000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((453457661 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((12046542339 : ℚ)/12500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((453457661 : ℚ)/25000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 22283980418103875927368117782375744000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22283980418103875927368117782375744000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (40 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 44567960836207751854736235564751488000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 13246136946246172362855033957869160000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (40 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 13246136946246172362855033957869160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (426282708052298117175713360939 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 45675700689400303928673855978822854531274264000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 729653565828406097705216970207466290937451472000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 45675700689400303928673855978822854531274264000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 45675700689400303928673855978822854531274264000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 729653565828406097705216970207466290937451472000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 45675700689400303928673855978822854531274264000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 821004967207206705562564682165112000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((55633890797 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((444366109203 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((55633890797 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_40_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 54280487122603715756424129877548000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54280487122603715756424129877548000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 54280487122603715756424129877548000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54280487122603715756424129877548000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 108560974245207431512848259755096000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (202592252656077549901414086510 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 216472957377730819679319322755339298789298928000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9924893853114035582755261151181881402421402144000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 216472957377730819679319322755339298789298928000000000000 else 0 := by
    intro v
    rw [hgrp1 (41 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 10357839767869497222113899796692560000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((14684247203688794403699 : ℚ)/702614689105000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((336623097348811205596301 : ℚ)/351307344552500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((14684247203688794403699 : ℚ)/702614689105000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 264132251682373404648253087908396000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 264132251682373404648253087908396000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (41 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 528264503364746809296506175816792000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 4846504348962311660569722300600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4846504348962311660569722300600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 4846504348962311660569722300600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 561558192778868886993943589747448000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 561558192778868886993943589747448000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (41 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1123116385557737773987887179494896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 297425941096495482345690501839052000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 297425941096495482345690501839052000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 297425941096495482345690501839052000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 297425941096495482345690501839052000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 594851882192990964691381003678104000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 4846504348962311660569722300600000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (41 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4846504348962311660569722300600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (375057927577174408739487976251 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 99375616349113537194188657239095194211068160000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1929332384576488679672809085238257611577863680000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 99375616349113537194188657239095194211068160000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 99375616349113537194188657239095194211068160000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1929332384576488679672809085238257611577863680000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 99375616349113537194188657239095194211068160000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2128083617274715754061186399716448000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1167430823 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((11332569177 : ℚ)/12500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1167430823 : ℚ)/25000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (315793081212774405782435575667 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 78949112319447128816986609033150361331851616000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1970185392635821496427213181650147277336296768000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 78949112319447128816986609033150361331851616000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 78949112319447128816986609033150361331851616000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1970185392635821496427213181650147277336296768000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 78949112319447128816986609033150361331851616000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2128083617274715754061186399716448000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((37098689017 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462901310983 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37098689017 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 264132251682373404648253087908396000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 264132251682373404648253087908396000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 264132251682373404648253087908396000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 264132251682373404648253087908396000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 528264503364746809296506175816792000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 4846504348962311660569722300600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 4846504348962311660569722300600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 4846504348962311660569722300600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 594851882192990964691381003678104000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (41 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 594851882192990964691381003678104000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 4379010326979764138674609786396452000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4379010326979764138674609786396452000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (41 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 8758020653959528277349219572792904000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 2722935499467706718752567403394552000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (41 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2722935499467706718752567403394552000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_41_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (347755948844868987344289356628 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 204418547768728837331702416500025259694000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4437667253424853985906317467599949480612000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 204418547768728837331702416500025259694000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 204418547768728837331702416500025259694000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4437667253424853985906317467599949480612000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 204418547768728837331702416500025259694000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 4846504348962311660569722300600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((4217855449 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((45782144551 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4217855449 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 402754727422315847974161687794570000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 402754727422315847974161687794570000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (42 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 805509454844631695948323375589140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 21318149309785332909019171455460000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 21318149309785332909019171455460000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 21318149309785332909019171455460000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (18364692577926283099068779560 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 32752435491070436976732766278099178210532720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 27524566772141055774451324286592021643578934560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 32752435491070436976732766278099178210532720000000000000 else 0 := by
    intro v
    rw [hgrp1 (42 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 27590071643123196648404789819148220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((296777369 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((124703222631 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((296777369 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 2029044061362713188998933816903590000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2029044061362713188998933816903590000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2029044061362713188998933816903590000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2029044061362713188998933816903590000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 4058088122725426377997867633807180000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 2029044061362713188998933816903590000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2029044061362713188998933816903590000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (42 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4058088122725426377997867633807180000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (378227105903078954687885708433 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 1303151299337730870515225590275482560108439000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24983769044447734907374338638597254879783122000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1303151299337730870515225590275482560108439000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1303151299337730870515225590275482560108439000000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24983769044447734907374338638597254879783122000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1303151299337730870515225590275482560108439000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 27590071643123196648404789819148220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((944652349 : ℚ)/20000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((9055347651 : ℚ)/10000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((944652349 : ℚ)/20000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 21318149309785332909019171455460000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (42 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 21318149309785332909019171455460000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_1_7 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 402754727422315847974161687794570000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 402754727422315847974161687794570000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 402754727422315847974161687794570000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 402754727422315847974161687794570000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 805509454844631695948323375589140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 402754727422315847974161687794570000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 402754727422315847974161687794570000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 402754727422315847974161687794570000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 402754727422315847974161687794570000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 805509454844631695948323375589140000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 21318149309785332909019171455460000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 21318149309785332909019171455460000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 21318149309785332909019171455460000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 15824079882924311513201328726477700000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 15824079882924311513201328726477700000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (42 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 31648159765848623026402657452955400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 32453669220693254722350980828544540000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (42 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 32453669220693254722350980828544540000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_42_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 10659074654892666454509585727730000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10659074654892666454509585727730000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 10659074654892666454509585727730000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 10659074654892666454509585727730000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 21318149309785332909019171455460000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (227798963190319442582713625621 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 13181604427304675894223521921258832642845612000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 516882541751732140355760500022238334714308776000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13181604427304675894223521921258832642845612000000000000 else 0 := by
    intro v
    rw [hgrp1 (43 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 543245750606341492144207543864756000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((11958585990096680572177 : ℚ)/492842207351000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((234462517685403319427823 : ℚ)/246421103675500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11958585990096680572177 : ℚ)/492842207351000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 174666000745056497910780054079360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 174666000745056497910780054079360000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (43 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 349332001490112995821560108158720000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 7889828391912116933792456135244000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7889828391912116933792456135244000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 7889828391912116933792456135244000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 3944914195956058466896228067622000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3944914195956058466896228067622000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (43 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7889828391912116933792456135244000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 96956874558114248161323717853018000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 96956874558114248161323717853018000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 96956874558114248161323717853018000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 96956874558114248161323717853018000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 193913749116228496322647435706036000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (304687987555522157707906542296 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 6861869453772986787225409992884079778028972000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 180190010208682522748196615720267840443942056000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6861869453772986787225409992884079778028972000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6861869453772986787225409992884079778028972000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 180190010208682522748196615720267840443942056000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6861869453772986787225409992884079778028972000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 193913749116228496322647435706036000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((35386193527 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((464613806473 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((35386193527 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 174666000745056497910780054079360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 174666000745056497910780054079360000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 174666000745056497910780054079360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 174666000745056497910780054079360000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 349332001490112995821560108158720000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 7889828391912116933792456135244000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 2 ⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7889828391912116933792456135244000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 7889828391912116933792456135244000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 7889828391912116933792456135244000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (43 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7889828391912116933792456135244000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 174666000745056497910780054079360000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 174666000745056497910780054079360000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (43 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 349332001490112995821560108158720000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_43_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 193913749116228496322647435706036000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (43 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 193913749116228496322647435706036000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_44_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 358536591684283585256344592953812000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 358536591684283585256344592953812000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (44 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 717073183368567170512689185907624000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_2_44_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 28831832033445155791938777186978000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 2 1 ⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 28831832033445155791938777186978000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inl ⟨⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 28831832033445155791938777186978000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
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
    (regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (4368716790414123879312362 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (340038785473895137666573645465 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (126853399990626014245543099 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-35 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (342174798412163354704642674823 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(38 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (351608687166216478644883091734 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370611240648506903188358471147 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5070859287181971992510909971 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (96354281358297841788661651403 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (404234177990123790920497863946 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (251291806442747958114693906966 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (181069906593781779461964407231 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (426282708052298117175713360939 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (202592252656077549901414086510 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (375057927577174408739487976251 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (315793081212774405782435575667 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (347755948844868987344289356628 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (18364692577926283099068779560 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (378227105903078954687885708433 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (227798963190319442582713625621 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (304687987555522157707906542296 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inl ⟨⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inl ⟨⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) :=
  ⟨L3C.cp_2_38_1_0, L3C.cp_2_38_1_1, L3C.cp_2_38_1_2, L3C.cp_2_38_1_3, L3C.cp_2_38_1_4, L3C.cp_2_38_1_5, L3C.cp_2_38_2_0, L3C.cp_2_38_2_1, L3C.cp_2_38_2_2, L3C.cp_2_38_2_3, L3C.cp_2_38_2_4, L3C.cp_2_38_2_5, L3C.cp_2_38_2_6, L3C.cp_2_39_1_0, L3C.cp_2_39_1_1, L3C.cp_2_39_1_2, L3C.cp_2_39_1_3, L3C.cp_2_39_1_4, L3C.cp_2_39_2_0, L3C.cp_2_39_2_1, L3C.cp_2_39_2_2, L3C.cp_2_39_2_3, L3C.cp_2_39_2_4, L3C.cp_2_39_2_5, L3C.cp_2_39_2_6, L3C.cp_2_39_2_7, L3C.cp_2_40_1_0, L3C.cp_2_40_1_1, L3C.cp_2_40_1_2, L3C.cp_2_40_1_3, L3C.cp_2_40_1_4, L3C.cp_2_40_1_5, L3C.cp_2_40_1_6, L3C.cp_2_40_2_0, L3C.cp_2_40_2_1, L3C.cp_2_40_2_2, L3C.cp_2_40_2_3, L3C.cp_2_40_2_4, L3C.cp_2_40_2_5, L3C.cp_2_40_2_6, L3C.cp_2_41_1_0, L3C.cp_2_41_1_1, L3C.cp_2_41_1_2, L3C.cp_2_41_1_3, L3C.cp_2_41_1_4, L3C.cp_2_41_1_5, L3C.cp_2_41_1_6, L3C.cp_2_41_2_0, L3C.cp_2_41_2_1, L3C.cp_2_41_2_2, L3C.cp_2_41_2_3, L3C.cp_2_41_2_4, L3C.cp_2_41_2_5, L3C.cp_2_41_2_6, L3C.cp_2_42_1_0, L3C.cp_2_42_1_1, L3C.cp_2_42_1_2, L3C.cp_2_42_1_3, L3C.cp_2_42_1_4, L3C.cp_2_42_1_5, L3C.cp_2_42_1_6, L3C.cp_2_42_1_7, L3C.cp_2_42_2_0, L3C.cp_2_42_2_1, L3C.cp_2_42_2_2, L3C.cp_2_42_2_3, L3C.cp_2_42_2_4, L3C.cp_2_43_1_0, L3C.cp_2_43_1_1, L3C.cp_2_43_1_2, L3C.cp_2_43_1_3, L3C.cp_2_43_1_4, L3C.cp_2_43_2_0, L3C.cp_2_43_2_1, L3C.cp_2_43_2_2, L3C.cp_2_43_2_3, L3C.cp_2_43_2_4, L3C.cp_2_43_2_5, L3C.cp_2_44_1_0, L3C.cp_2_44_1_1⟩
