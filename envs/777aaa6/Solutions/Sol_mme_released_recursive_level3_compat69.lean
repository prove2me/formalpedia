-- Prove2me | solution 1 for mme_released_recursive_level3_compat69
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T15:54:11.872284+00:00
-- url     : https://prove2.me/submissions/525c1404-e04b-4911-ab7b-82e0f977e187

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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 5 1 ⟨rr, c⟩ w else 0 := by
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
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 5 2 ⟨rr, c⟩ w else 0 := by
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


theorem cp_5_59_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 772933773019936056175076994085830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 772933773019936056175076994085830000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (59 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1545867546039872112350153988171660000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_59_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 2327095923012045268811909834160420000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (59 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2327095923012045268811909834160420000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 42247323910328405110407379943820000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42247323910328405110407379943820000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (60 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84494647820656810220814759887640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 25138194595738044609185240112360000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25138194595738044609185240112360000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 25138194595738044609185240112360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (30359237589013054662649623 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 25801340169173614225975546746524056800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25138142993057706261956788161266506951886400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 25801340169173614225975546746524056800000000000000 else 0 := by
    intro v
    rw [hgrp1 (60 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25138194595738044609185240112360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((51319 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((24999948681 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51319 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42247323910328405110407379943820000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42247323910328405110407379943820000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42247323910328405110407379943820000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42247323910328405110407379943820000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 84494647820656810220814759887640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 42247323910328405110407379943820000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42247323910328405110407379943820000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42247323910328405110407379943820000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42247323910328405110407379943820000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84494647820656810220814759887640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 25138194595738044609185240112360000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25138194595738044609185240112360000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 25138194595738044609185240112360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 12569097297869022304592620056180000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12569097297869022304592620056180000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (60 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25138194595738044609185240112360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_60_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 84494647820656810220814759887640000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (60 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84494647820656810220814759887640000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 303165231579730152199112445025596000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 303165231579730152199112445025596000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (61 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 606330463159460304398224890051192000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 924772555692650620451687004070020000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (61 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 924772555692650620451687004070020000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 166081915862127180133887554974404000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 166081915862127180133887554974404000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 166081915862127180133887554974404000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 166081915862127180133887554974404000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 332163831724254360267775109948808000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 13721739191064044214312995929980000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13721739191064044214312995929980000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) x = 13721739191064044214312995929980000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 13721739191064044214312995929980000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (61 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 13721739191064044214312995929980000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319501305154271677087811261982 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 12514779687318028745743038650957770612410720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 307134272349618302776289032646892458775178560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 12514779687318028745743038650957770612410720000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 12514779687318028745743038650957770612410720000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 307134272349618302776289032646892458775178560000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 12514779687318028745743038650957770612410720000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 332163831724254360267775109948808000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1883826367 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((23116173633 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1883826367 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 296304361984198130091955947060606000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 296304361984198130091955947060606000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (61 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 592608723968396260183911894121212000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 296304361984198130091955947060606000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 296304361984198130091955947060606000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 296304361984198130091955947060606000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 296304361984198130091955947060606000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 592608723968396260183911894121212000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 332163831724254360267775109948808000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (61 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 332163831724254360267775109948808000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_61_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 13721739191064044214312995929980000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 13721739191064044214312995929980000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 13721739191064044214312995929980000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (4285041861253412157081214 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 283541655098782466684818781049809614440000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2233853796844155698924488776517237900380771120000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 283541655098782466684818781049809614440000000000000 else 0 := by
    intro v
    rw [hgrp1 (62 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2233854363927465896489422146154800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((9868484305785217 : ℚ)/77747859390000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((38873919826515694214783 : ℚ)/38873929695000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((9868484305785217 : ℚ)/77747859390000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 17093047735059317643225043104372180000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 17093047735059317643225043104372180000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (62 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 34186095470118635286450086208744360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 10432241252819340223507351247847240000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (62 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 10432241252819340223507351247847240000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (340001885816773461959176473242 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 336313733212057429497586504513796793121777920000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7545076994216268482847770862407286413756444160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 336313733212057429497586504513796793121777920000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 336313733212057429497586504513796793121777920000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7545076994216268482847770862407286413756444160000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 336313733212057429497586504513796793121777920000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 8217704460640383341842943871434880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((20462754217 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((229537245783 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20462754217 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 1187430327999172903762590878038140000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1187430327999172903762590878038140000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1187430327999172903762590878038140000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1187430327999172903762590878038140000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2374860655998345807525181756076280000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 19317571748509014825014769742440000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 19317571748509014825014769742440000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) x = 19317571748509014825014769742440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (125062099026323270542177968 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 91062975269756250358075149521552932680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 19317389622558475312514053592140956894134640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 91062975269756250358075149521552932680000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 91062975269756250358075149521552932680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 19317389622558475312514053592140956894134640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 91062975269756250358075149521552932680000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 19317571748509014825014769742440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((4713997 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((499995286003 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4713997 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 2374860655998345807525181756076280000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (62 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2374860655998345807525181756076280000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 17012885803149623180294655914540220000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 17012885803149623180294655914540220000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (62 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 34025771606299246360589311829080440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (342215644469666723789004189236 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 339242375557599184704457576945047804354812160000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7539219709525184972434028717544784391290375680000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 339242375557599184704457576945047804354812160000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 339242375557599184704457576945047804354812160000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 7539219709525184972434028717544784391290375680000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 339242375557599184704457576945047804354812160000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 8217704460640383341842943871434880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((20640945241 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((229359054759 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((20640945241 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 10592565116638729149368125627511160000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (62 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 10592565116638729149368125627511160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 1107268396089478440832203688206180000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1107268396089478440832203688206180000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1107268396089478440832203688206180000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1107268396089478440832203688206180000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 2214536792178956881664407376412360000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_62_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 19317571748509014825014769742440000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 19317571748509014825014769742440000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 19317571748509014825014769742440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (95489118098971434015137804258 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 200838854029811454030974290275567371764678730000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 23952751699683829738274931082059555256470642540000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 200838854029811454030974290275567371764678730000000000000 else 0 := by
    intro v
    rw [hgrp1 (63 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 24354429407743452646336879662610690000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((5336858442352048933079 : ℚ)/647166320587000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((318246301851147951066921 : ℚ)/323583160293500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((5336858442352048933079 : ℚ)/647166320587000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 56968193527786898415375507649830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 56968193527786898415375507649830000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (63 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 113936387055573796830751015299660000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 17919171462815045460303200047674000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 17919171462815045460303200047674000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (63 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 35838342925630090920606400095348000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 430617963309328372306898071705050000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 430617963309328372306898071705050000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 430617963309328372306898071705050000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 430617963309328372306898071705050000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 861235926618656744613796143410100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 975172313674230541444547158709760000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (63 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 975172313674230541444547158709760000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (404152306767389683355699467182 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 636035735632458858647249276760064587599623950000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11030738496561714195794074625159420824800752100000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 636035735632458858647249276760064587599623950000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 636035735632458858647249276760064587599623950000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11030738496561714195794074625159420824800752100000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 636035735632458858647249276760064587599623950000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 12302809967826631913088573178679550000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((51698411769 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((448301588231 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((51698411769 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 409448224969996819409526372971120000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 409448224969996819409526372971120000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 409448224969996819409526372971120000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 409448224969996819409526372971120000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 818896449939993638819052745942240000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (249740798198116262833109372162 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 22361862272532438869316167312500837630839680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 774172725394928761080420411317238324738320640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 22361862272532438869316167312500837630839680000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 22361862272532438869316167312500837630839680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 774172725394928761080420411317238324738320640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 22361862272532438869316167312500837630839680000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 818896449939993638819052745942240000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((6826828433 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((118173171567 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6826828433 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 56968193527786898415375507649830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 56968193527786898415375507649830000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 56968193527786898415375507649830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 56968193527786898415375507649830000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 113936387055573796830751015299660000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (181441351400376553179138100488 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 223727471435731540505105285929417399700658600000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11855355024955168832078362606820715200598682800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 223727471435731540505105285929417399700658600000000000000 else 0 := by
    intro v
    rw [hgrp2 (63 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 12302809967826631913088573178679550000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((4546267723 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((120453732277 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((4546267723 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 23535532957803459007517826916668450000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 23535532957803459007517826916668450000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (63 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 47071065915606918015035653833336900000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 13982942344385282296521422068031890000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (63 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 13982942344385282296521422068031890000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (426278380718519975826627576145 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 47913233027747883899442720450089130116438400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 765409460563160976814910702509921739767123200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 47913233027747883899442720450089130116438400000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 47913233027747883899442720450089130116438400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 765409460563160976814910702509921739767123200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 47913233027747883899442720450089130116438400000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 861235926618656744613796143410100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1738534687 : ℚ)/31250000000) else if 3 * (v 0).val + (v 1).val = 4 then ((13886465313 : ℚ)/15625000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1738534687 : ℚ)/31250000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_63_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 56968193527786898415375507649830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 56968193527786898415375507649830000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 56968193527786898415375507649830000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 56968193527786898415375507649830000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 113936387055573796830751015299660000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (188396088087661719202622019915 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 37936434350140398390873202544670609029775520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1913822114901088380483807959969138781940448960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 37936434350140398390873202544670609029775520000000000000 else 0 := by
    intro v
    rw [hgrp1 (64 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1989694983601369177265554365058480000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((6765658143936354177497 : ℚ)/354846107715500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((170657395713813645822503 : ℚ)/177423053857750000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6765658143936354177497 : ℚ)/354846107715500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 47601760373360615015284362040480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 47601760373360615015284362040480000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (64 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 95203520746721230030568724080960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 893625539451978811421301757160000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 893625539451978811421301757160000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 893625539451978811421301757160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 100589547469435162469269769584900000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 100589547469435162469269769584900000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (64 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 201179094938870324938539539169800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 52987787096074547453985407544420000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 52987787096074547453985407544420000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 52987787096074547453985407544420000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 52987787096074547453985407544420000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 105975574192149094907970815088840000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 893625539451978811421301757160000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (64 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 893625539451978811421301757160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370511894091093269979178764573 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 18821697487901927774677845937535469408530800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 372118841364775463765168261212529061182938400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18821697487901927774677845937535469408530800000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18821697487901927774677845937535469408530800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 372118841364775463765168261212529061182938400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18821697487901927774677845937535469408530800000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 409762236340579319314523953087600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((45933216433 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((454066783567 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((45933216433 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (302955218006102328592512063211 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 14391427938562831959499234545976707882680800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 380979380463453655395525483995646584234638400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 14391427938562831959499234545976707882680800000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 14391427938562831959499234545976707882680800000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 380979380463453655395525483995646584234638400000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 14391427938562831959499234545976707882680800000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 409762236340579319314523953087600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((17560705529 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((232439294471 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((17560705529 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 47601760373360615015284362040480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 47601760373360615015284362040480000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 47601760373360615015284362040480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 47601760373360615015284362040480000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 95203520746721230030568724080960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 893625539451978811421301757160000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 893625539451978811421301757160000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 893625539451978811421301757160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 105975574192149094907970815088840000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (64 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 105975574192149094907970815088840000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 837568134003755543990799568025920000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 837568134003755543990799568025920000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (64 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1675136268007511087981599136051840000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 515737810532728414222494768176440000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (64 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 515737810532728414222494768176440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_64_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (345885938136950246525113192650 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 37420698229736468982249885210709094455880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 818784142992505873456801986738581811088240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 37420698229736468982249885210709094455880000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 37420698229736468982249885210709094455880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 818784142992505873456801986738581811088240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 37420698229736468982249885210709094455880000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 893625539451978811421301757160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((41875144093 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((458124855907 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((41875144093 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 20815663064782442735024958692691615000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 20815663064782442735024958692691615000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (65 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 41631326129564885470049917385383230000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (207797016739708558506655661130 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 246695861011329542097845517221584341027547578000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10936841607046302026065785437032065317944904844000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 246695861011329542097845517221584341027547578000000000000 else 0 := by
    intro v
    rw [hgrp1 (65 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11430233329068961110261476471475234000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((2484684966510961980043 : ℚ)/115123653879000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((55077141972989038019957 : ℚ)/57561826939500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2484684966510961980043 : ℚ)/115123653879000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 12225284390445578544295299510935210000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (65 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 12225284390445578544295299510935210000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (399697866257187199462958569559 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 40484082430873492770230636056146795881093048000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 714082896514870448493361767347682408237813904000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 40484082430873492770230636056146795881093048000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 40484082430873492770230636056146795881093048000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 714082896514870448493361767347682408237813904000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 40484082430873492770230636056146795881093048000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 795051061376617434033823039459976000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((50920103623 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((449079896377 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((50920103623 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 54577643036136553761741796373175000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54577643036136553761741796373175000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 54577643036136553761741796373175000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54577643036136553761741796373175000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 109155286072273107523483592746350000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 54577643036136553761741796373175000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 54577643036136553761741796373175000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 54577643036136553761741796373175000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 54577643036136553761741796373175000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 109155286072273107523483592746350000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (416226441690597092722607245975 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 39918322631901272502124361686017010617518418000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 661708064914853077947604219049723978764963164000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39918322631901272502124361686017010617518418000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39918322631901272502124361686017010617518418000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 661708064914853077947604219049723978764963164000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39918322631901272502124361686017010617518418000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 741544710178655622951852942421758000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((53831309271 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446168690729 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53831309271 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 397525530688308717016911519729988000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 397525530688308717016911519729988000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 397525530688308717016911519729988000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 397525530688308717016911519729988000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 795051061376617434033823039459976000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 20761085421746306181263216896318440000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (65 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 20761085421746306181263216896318440000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 15724887020318305834286420212685958000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 15724887020318305834286420212685958000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (65 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 31449774040636611668572840425371916000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (434224377014837342720231636657 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 610050507250130875103895681821701921791154116000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9468587604390043737101832165410072156417691768000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 610050507250130875103895681821701921791154116000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 610050507250130875103895681821701921791154116000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9468587604390043737101832165410072156417691768000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 610050507250130875103895681821701921791154116000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 10688688618890305487309623529053476000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((57074401641 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((442925598359 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((57074401641 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 904206347448890541557306632206326000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (65 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 904206347448890541557306632206326000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_65_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 370772355089327811475926471210879000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 370772355089327811475926471210879000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 370772355089327811475926471210879000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 370772355089327811475926471210879000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 741544710178655622951852942421758000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 4646943431783900206368000000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (66 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4646943431783900206368000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 2321944764939493499536407164395728000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2321944764939493499536407164395728000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (66 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4643889529878986999072814328791456000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 1526950952456603647592835604272000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1526950952456603647592835604272000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 1 ⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 1526950952456603647592835604272000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1526950952456603647592835604272000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 3053901904913207295185671208544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 3053901904913207295185671208544000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 3053901904913207295185671208544000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 3053901904913207295185671208544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 58248150696001958602299154079952000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 58248150696001958602299154079952000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 58248150696001958602299154079952000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 58248150696001958602299154079952000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 116496301392003917204598308159904000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_5_66_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 302909800343517731221960066419072000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 302909800343517731221960066419072000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 5 2 ⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 302909800343517731221960066419072000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 302909800343517731221960066419072000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 605819600687035462443920132838144000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
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
    (regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (30359237589013054662649623 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319501305154271677087811261982 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -4 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (4285041861253412157081214 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (340001885816773461959176473242 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (125062099026323270542177968 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (342215644469666723789004189236 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -3 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (95489118098971434015137804258 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (404152306767389683355699467182 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (249740798198116262833109372162 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (181441351400376553179138100488 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (426278380718519975826627576145 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (188396088087661719202622019915 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -2 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370511894091093269979178764573 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (302955218006102328592512063211 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (345885938136950246525113192650 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (207797016739708558506655661130 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (399697866257187199462958569559 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (416226441690597092722607245975 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (434224377014837342720231636657 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inl ⟨⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) :=
  ⟨L3C.cp_5_59_2_2, L3C.cp_5_59_2_3, L3C.cp_5_60_1_0, L3C.cp_5_60_1_1, L3C.cp_5_60_1_2, L3C.cp_5_60_1_3, L3C.cp_5_60_2_0, L3C.cp_5_60_2_1, L3C.cp_5_60_2_2, L3C.cp_5_60_2_3, L3C.cp_5_61_1_0, L3C.cp_5_61_1_1, L3C.cp_5_61_1_2, L3C.cp_5_61_1_3, L3C.cp_5_61_2_0, L3C.cp_5_61_2_1, L3C.cp_5_61_2_2, L3C.cp_5_61_2_3, L3C.cp_5_61_2_4, L3C.cp_5_61_2_5, L3C.cp_5_62_1_0, L3C.cp_5_62_1_1, L3C.cp_5_62_1_2, L3C.cp_5_62_1_3, L3C.cp_5_62_1_4, L3C.cp_5_62_1_5, L3C.cp_5_62_2_0, L3C.cp_5_62_2_1, L3C.cp_5_62_2_2, L3C.cp_5_62_2_3, L3C.cp_5_62_2_4, L3C.cp_5_62_2_5, L3C.cp_5_62_2_6, L3C.cp_5_63_1_0, L3C.cp_5_63_1_1, L3C.cp_5_63_1_2, L3C.cp_5_63_1_3, L3C.cp_5_63_1_4, L3C.cp_5_63_1_5, L3C.cp_5_63_1_6, L3C.cp_5_63_2_0, L3C.cp_5_63_2_1, L3C.cp_5_63_2_2, L3C.cp_5_63_2_3, L3C.cp_5_63_2_4, L3C.cp_5_63_2_5, L3C.cp_5_63_2_6, L3C.cp_5_64_1_0, L3C.cp_5_64_1_1, L3C.cp_5_64_1_2, L3C.cp_5_64_1_3, L3C.cp_5_64_1_4, L3C.cp_5_64_1_5, L3C.cp_5_64_1_6, L3C.cp_5_64_2_0, L3C.cp_5_64_2_1, L3C.cp_5_64_2_2, L3C.cp_5_64_2_3, L3C.cp_5_64_2_4, L3C.cp_5_64_2_5, L3C.cp_5_64_2_6, L3C.cp_5_65_1_0, L3C.cp_5_65_1_1, L3C.cp_5_65_1_2, L3C.cp_5_65_1_3, L3C.cp_5_65_1_4, L3C.cp_5_65_2_0, L3C.cp_5_65_2_1, L3C.cp_5_65_2_2, L3C.cp_5_65_2_3, L3C.cp_5_65_2_4, L3C.cp_5_65_2_5, L3C.cp_5_65_2_6, L3C.cp_5_65_2_7, L3C.cp_5_66_1_0, L3C.cp_5_66_1_1, L3C.cp_5_66_1_2, L3C.cp_5_66_2_0, L3C.cp_5_66_2_1, L3C.cp_5_66_2_2⟩
