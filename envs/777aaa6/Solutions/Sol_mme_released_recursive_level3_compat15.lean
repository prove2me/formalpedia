-- Prove2me | solution 1 for mme_released_recursive_level3_compat15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T08:52:42.280986+00:00
-- url     : https://prove2.me/submissions/f3de0e4c-bdb5-4406-ac56-d9406adfaab0

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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 1 1 ⟨rr, c⟩ w else 0 := by
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
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 1 2 ⟨rr, c⟩ w else 0 := by
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


theorem cp_1_14_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 84545411924533609104249095516376000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (14 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84545411924533609104249095516376000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_14_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 26269185024483463463750904483624000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 26269185024483463463750904483624000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 26269185024483463463750904483624000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 42170801964900014297550394263600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42170801964900014297550394263600000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (15 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84341603929800028595100788527200000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 25827634099926630804899211472800000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25827634099926630804899211472800000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 25827634099926630804899211472800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (179757265175770871934140766963 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 464207775728757385760004203531104765377600000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 24899218548469116033379203065737790469244800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 464207775728757385760004203531104765377600000000000000 else 0 := by
    intro v
    rw [hgrp1 (15 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25827634099926630804899211472800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((8986649221 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((241013350779 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((8986649221 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42170801964900014297550394263600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42170801964900014297550394263600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42170801964900014297550394263600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42170801964900014297550394263600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 84341603929800028595100788527200000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 42170801964900014297550394263600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42170801964900014297550394263600000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42170801964900014297550394263600000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42170801964900014297550394263600000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84341603929800028595100788527200000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 25827634099926630804899211472800000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25827634099926630804899211472800000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 25827634099926630804899211472800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 12913817049963315402449605736400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12913817049963315402449605736400000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (15 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25827634099926630804899211472800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_15_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 84341603929800028595100788527200000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (15 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84341603929800028595100788527200000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (227713116289661668050286534912 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 13226148485052550798035359570866218794591160000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 518892137211337964027347365337167562410817680000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13226148485052550798035359570866218794591160000000000000 else 0 := by
    intro v
    rw [hgrp1 (16 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 545344434181443065623418084478900000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((5976086807642688983297 : ℚ)/246407764317500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((117227795351107311016703 : ℚ)/123203882158750000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((5976086807642688983297 : ℚ)/246407764317500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 175369357066913318848443498027285000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 175369357066913318848443498027285000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (16 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 350738714133826637696886996054570000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 7950259770204095446581915521100000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 7950259770204095446581915521100000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 7950259770204095446581915521100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 3975129885102047723290957760550000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3975129885102047723290957760550000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (16 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7950259770204095446581915521100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 97302860023808213963265544212165000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 97302860023808213963265544212165000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 97302860023808213963265544212165000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 97302860023808213963265544212165000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 194605720047616427926531088424330000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (304642746381575872403725825436 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 6885008674491856588471990200326476843080810000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 180835702698632714749587108023677046313838380000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6885008674491856588471990200326476843080810000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 6885008674491856588471990200326476843080810000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 180835702698632714749587108023677046313838380000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 6885008674491856588471990200326476843080810000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 194605720047616427926531088424330000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((35379271857 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((464620728143 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((35379271857 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 175369357066913318848443498027285000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 175369357066913318848443498027285000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 175369357066913318848443498027285000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 175369357066913318848443498027285000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 350738714133826637696886996054570000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 7950259770204095446581915521100000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 7950259770204095446581915521100000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 7950259770204095446581915521100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 7950259770204095446581915521100000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (16 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 7950259770204095446581915521100000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 175369357066913318848443498027285000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 175369357066913318848443498027285000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (16 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 350738714133826637696886996054570000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_16_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 194605720047616427926531088424330000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (16 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 194605720047616427926531088424330000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 171314558056452993796685202387840000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (17 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 171314558056452993796685202387840000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 3340811561779632224181657398806080000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3340811561779632224181657398806080000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (17 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6681623123559264448363314797612160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (351626468835661830110592854136 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 286033714825114399829201353361885461600178880000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6109555693909035648704912090888389076799642240000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 286033714825114399829201353361885461600178880000000000000 else 0 := by
    intro v
    rw [hgrp1 (17 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6681623123559264448363314797612160000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((10434711656303731968317 : ℚ)/243750324094000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((111440450390696268031683 : ℚ)/121875162047000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((10434711656303731968317 : ℚ)/243750324094000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 83421285495345250637064651347400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83421285495345250637064651347400000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (17 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 166842570990690501274129302694800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 2235993532881246261277949846520000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2235993532881246261277949846520000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2235993532881246261277949846520000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2235993532881246261277949846520000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 4471987065762492522555899693040000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 4471987065762492522555899693040000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4471987065762492522555899693040000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 4471987065762492522555899693040000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 420887307016115598453613925572440000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 420887307016115598453613925572440000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 420887307016115598453613925572440000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 420887307016115598453613925572440000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 841774614032231196907227851144880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370634039836293079809772007203 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 268362552944598093380581160397009258101912640000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5303123403637837064694924625673261483796174720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 268362552944598093380581160397009258101912640000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 268362552944598093380581160397009258101912640000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5303123403637837064694924625673261483796174720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 268362552944598093380581160397009258101912640000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 5839848509527033251456086946467280000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((11488420997 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113511579003 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11488420997 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 83421285495345250637064651347400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 83421285495345250637064651347400000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 83421285495345250637064651347400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 83421285495345250637064651347400000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 166842570990690501274129302694800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 83421285495345250637064651347400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83421285495345250637064651347400000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 83421285495345250637064651347400000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 83421285495345250637064651347400000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 166842570990690501274129302694800000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5072577080508898494080380955 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 1610739062024076335597329418384184081164640000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5836627031402985098784892287630511631837670720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1610739062024076335597329418384184081164640000000000000 else 0 := by
    intro v
    rw [hgrp2 (17 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 5839848509527033251456086946467280000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((137909319 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249862090681 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((137909319 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 420887307016115598453613925572440000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 420887307016115598453613925572440000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (17 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 841774614032231196907227851144880000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_17_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 4471987065762492522555899693040000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (17 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4471987065762492522555899693040000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 1390994858627270785074470745439084000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (18 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1390994858627270785074470745439084000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 2484214895806145030899529254560916000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 2484214895806145030899529254560916000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (18 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4968429791612290061799058509121832000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (374475240246384527152661269385 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 64819031168655337068397530711089929249485728000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1261356796289960110937675684016904141501028544000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 64819031168655337068397530711089929249485728000000000000 else 0 := by
    intro v
    rw [hgrp1 (18 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1390994858627270785074470745439084000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((1045411656338399229967 : ℚ)/22434186579125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((10171681633224100770033 : ℚ)/11217093289562500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1045411656338399229967 : ℚ)/22434186579125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 51073197650556117812410385579568000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 51073197650556117812410385579568000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 51073197650556117812410385579568000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 1242107447903072515449764627280458000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1242107447903072515449764627280458000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1242107447903072515449764627280458000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1242107447903072515449764627280458000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2484214895806145030899529254560916000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (380230352524776246715623616251 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 63743035963375676306064951726828101191561808000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1212435589049963314649930456405859797616876384000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63743035963375676306064951726828101191561808000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 63743035963375676306064951726828101191561808000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1212435589049963314649930456405859797616876384000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 63743035963375676306064951726828101191561808000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 1339921660976714667262060359859516000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((11893052747 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113106947253 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11893052747 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 669960830488357333631030179929758000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 669960830488357333631030179929758000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 669960830488357333631030179929758000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 669960830488357333631030179929758000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 1339921660976714667262060359859516000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 2484214895806145030899529254560916000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (18 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2484214895806145030899529254560916000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_18_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 25536598825278058906205192789784000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 25536598825278058906205192789784000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (18 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 51073197650556117812410385579568000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 109598382243794462278000000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (19 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 109598382243794462278000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 54799191121897231139000000000000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 54799191121897231139000000000000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (19 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 109598382243794462278000000000000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 25206518857492081841369253621434000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25206518857492081841369253621434000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 25206518857492081841369253621434000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42195931693151190218315373189283000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42195931693151190218315373189283000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42195931693151190218315373189283000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42195931693151190218315373189283000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84391863386302380436630746378566000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42195931693151190218315373189283000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42195931693151190218315373189283000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42195931693151190218315373189283000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42195931693151190218315373189283000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 84391863386302380436630746378566000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_19_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (32560406242054022645786651 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 27888845355193244238436721376305277676000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25206463079801371454880776747991247389444648000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 27888845355193244238436721376305277676000000000000 else 0 := by
    intro v
    rw [hgrp2 (19 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25206518857492081841369253621434000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((553207 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249999446793 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((553207 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 359281994194949900515378876640806000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 359281994194949900515378876640806000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (20 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 718563988389899801030757753281612000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 28856729022621953760732734992492000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 28856729022621953760732734992492000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 28856729022621953760732734992492000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (152437542291207461352141803 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 7618093816293904492359263738229390204864000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1304411784655187517235524793198419541219590272000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 7618093816293904492359263738229390204864000000000000 else 0 := by
    intro v
    rw [hgrp1 (20 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1304427020842820105044509511725896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((730023 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((62499269977 : ℚ)/62500000000) else if 3 * (v 0).val + (v 1).val = 6 then ((730023 : ℚ)/125000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 652213510421410052522254755862948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 652213510421410052522254755862948000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 652213510421410052522254755862948000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 652213510421410052522254755862948000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 1304427020842820105044509511725896000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 14428364511310976880366367496246000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14428364511310976880366367496246000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (20 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 28856729022621953760732734992492000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (412649439548562291442808537739 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 38224642503738590335252696638488094451239244000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 642114703382422620360252360004635811097521512000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38224642503738590335252696638488094451239244000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 38224642503738590335252696638488094451239244000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 642114703382422620360252360004635811097521512000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 38224642503738590335252696638488094451239244000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 718563988389899801030757753281612000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((53195878337 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((446804121663 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((53195878337 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 359281994194949900515378876640806000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 359281994194949900515378876640806000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 359281994194949900515378876640806000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 359281994194949900515378876640806000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 718563988389899801030757753281612000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 28856729022621953760732734992492000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 28856729022621953760732734992492000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 28856729022621953760732734992492000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 666641874932721029402621123359194000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 666641874932721029402621123359194000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (20 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1333283749865442058805242246718388000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_20_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 2022991009232719906075267265007508000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (20 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2022991009232719906075267265007508000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (202589553459618648061425233068 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 231102304998608224176444390335512741517777520000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10595809674895412239899494166349982516964444960000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 231102304998608224176444390335512741517777520000000000000 else 0 := by
    intro v
    rw [hgrp1 (21 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11058014284892628688252382947021008000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((2936832039636809652679 : ℚ)/140524477446600000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((67325406683663190347321 : ℚ)/70262238723300000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2936832039636809652679 : ℚ)/140524477446600000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 281748770307784078493938327188552000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 281748770307784078493938327188552000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (21 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 563497540615568156987876654377104000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 5172714061608013218651789532080000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 5172714061608013218651789532080000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 5172714061608013218651789532080000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 599459599508554324814750129892024000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 599459599508554324814750129892024000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (21 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1198919199017108649629500259784048000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 317710829200770246320811802703472000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 317710829200770246320811802703472000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 317710829200770246320811802703472000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 317710829200770246320811802703472000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 635421658401540492641623605406944000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 5172714061608013218651789532080000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (21 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 5172714061608013218651789532080000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (375049718332162595038734587236 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 106093232013537949843418350352102344255346496000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2059819168245414682540476253642531311489307008000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 106093232013537949843418350352102344255346496000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 106093232013537949843418350352102344255346496000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2059819168245414682540476253642531311489307008000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 106093232013537949843418350352102344255346496000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2272005632272490582227312954346736000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((11673962259 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113326037741 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11673962259 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (315799227602756606051451259092 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 84290600902602243463450307386820501502914448000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2103424430467286095300412339573094996994171104000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 84290600902602243463450307386820501502914448000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 84290600902602243463450307386820501502914448000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2103424430467286095300412339573094996994171104000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 84290600902602243463450307386820501502914448000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2272005632272490582227312954346736000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((37099644343 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((462900355657 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((37099644343 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 281748770307784078493938327188552000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 281748770307784078493938327188552000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 281748770307784078493938327188552000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 281748770307784078493938327188552000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 563497540615568156987876654377104000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 5172714061608013218651789532080000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5172714061608013218651789532080000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 5172714061608013218651789532080000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 635421658401540492641623605406944000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (21 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 635421658401540492641623605406944000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 4674753096617853131506473323525688000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4674753096617853131506473323525688000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (21 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 9349506193235706263012946647051376000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 2907427290674031074868936559753680000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (21 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 2907427290674031074868936559753680000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_21_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (348615335646374344560918935577 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 218900212253474927893800932294368100087760000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4734913637101063362864187667491263799824480000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 218900212253474927893800932294368100087760000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 218900212253474927893800932294368100087760000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 4734913637101063362864187667491263799824480000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 218900212253474927893800932294368100087760000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 5172714061608013218651789532080000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((42318251047 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((457681748953 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((42318251047 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 12821205661254068760824353286868156000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (22 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 12821205661254068760824353286868156000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 22066885458972807055083646713131844000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 22066885458972807055083646713131844000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (22 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 44133770917945614110167293426263688000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371559365770661185761381445394 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 590142305946318172115009718984875935037750304000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 11618611651038258897498268478248104129924499392000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 590142305946318172115009718984875935037750304000000000000 else 0 := by
    intro v
    rw [hgrp1 (22 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 12798896262930895241728287916217856000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((704803901796371890787 : ℚ)/15285655568000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((6938023882203628109213 : ℚ)/7642827784000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((704803901796371890787 : ℚ)/15285655568000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (279468833231815538305885609416 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 704907229182467964841909447890177298549200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 20899583864808583166381551754519645402901600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 704907229182467964841909447890177298549200000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 1 ⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 704907229182467964841909447890177298549200000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 20899583864808583166381551754519645402901600000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 704907229182467964841909447890177298549200000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 22309398323173519096065370650300000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((7899218291 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((117100781709 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((7899218291 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 22309398323173519096065370650300000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 22309398323173519096065370650300000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 22309398323173519096065370650300000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 1265739441918242914044147955024848000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1265739441918242914044147955024848000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1265739441918242914044147955024848000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1265739441918242914044147955024848000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2531478883836485828088295910049696000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_1_22_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (407974182977566799520069341569 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 536155196934911105713512155158162516876822368000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9165546627844828556749573883178122966246355264000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 536155196934911105713512155158162516876822368000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 1 2 ⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 536155196934911105713512155158162516876822368000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9165546627844828556749573883178122966246355264000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 536155196934911105713512155158162516876822368000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 10237857021714650768176598193494448000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((26184932833 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((223815067167 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((26184932833 : ℚ)/500000000000) else 0 := by
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
    (regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(14 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (179757265175770871934140766963 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (227713116289661668050286534912 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 4 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (304642746381575872403725825436 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -7 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (351626468835661830110592854136 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (370634039836293079809772007203 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(17 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5072577080508898494080380955 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (374475240246384527152661269385 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (380230352524776246715623616251 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(18 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(19 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (32560406242054022645786651 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (152437542291207461352141803 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (412649439548562291442808537739 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 0 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (202589553459618648061425233068 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (375049718332162595038734587236 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (315799227602756606051451259092 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then -4 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (348615335646374344560918935577 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371559365770661185761381445394 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (279468833231815538305885609416 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inl ⟨⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (27 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (407974182977566799520069341569 : ℚ)/10^30) :=
  ⟨L3C.cp_1_14_2_2, L3C.cp_1_14_2_3, L3C.cp_1_15_1_0, L3C.cp_1_15_1_1, L3C.cp_1_15_1_2, L3C.cp_1_15_1_3, L3C.cp_1_15_2_0, L3C.cp_1_15_2_1, L3C.cp_1_15_2_2, L3C.cp_1_15_2_3, L3C.cp_1_16_1_0, L3C.cp_1_16_1_1, L3C.cp_1_16_1_2, L3C.cp_1_16_1_3, L3C.cp_1_16_1_4, L3C.cp_1_16_2_0, L3C.cp_1_16_2_1, L3C.cp_1_16_2_2, L3C.cp_1_16_2_3, L3C.cp_1_16_2_4, L3C.cp_1_16_2_5, L3C.cp_1_17_1_0, L3C.cp_1_17_1_1, L3C.cp_1_17_1_2, L3C.cp_1_17_1_3, L3C.cp_1_17_1_4, L3C.cp_1_17_2_0, L3C.cp_1_17_2_1, L3C.cp_1_17_2_2, L3C.cp_1_17_2_3, L3C.cp_1_17_2_4, L3C.cp_1_17_2_5, L3C.cp_1_17_2_6, L3C.cp_1_17_2_7, L3C.cp_1_18_1_0, L3C.cp_1_18_1_1, L3C.cp_1_18_1_2, L3C.cp_1_18_2_0, L3C.cp_1_18_2_1, L3C.cp_1_18_2_2, L3C.cp_1_18_2_3, L3C.cp_1_18_2_4, L3C.cp_1_18_2_5, L3C.cp_1_19_1_0, L3C.cp_1_19_1_1, L3C.cp_1_19_2_0, L3C.cp_1_19_2_1, L3C.cp_1_19_2_2, L3C.cp_1_19_2_3, L3C.cp_1_20_1_0, L3C.cp_1_20_1_1, L3C.cp_1_20_1_2, L3C.cp_1_20_1_3, L3C.cp_1_20_1_4, L3C.cp_1_20_1_5, L3C.cp_1_20_2_0, L3C.cp_1_20_2_1, L3C.cp_1_20_2_2, L3C.cp_1_20_2_3, L3C.cp_1_21_1_0, L3C.cp_1_21_1_1, L3C.cp_1_21_1_2, L3C.cp_1_21_1_3, L3C.cp_1_21_1_4, L3C.cp_1_21_1_5, L3C.cp_1_21_1_6, L3C.cp_1_21_2_0, L3C.cp_1_21_2_1, L3C.cp_1_21_2_2, L3C.cp_1_21_2_3, L3C.cp_1_21_2_4, L3C.cp_1_21_2_5, L3C.cp_1_21_2_6, L3C.cp_1_22_1_0, L3C.cp_1_22_1_1, L3C.cp_1_22_1_2, L3C.cp_1_22_1_3, L3C.cp_1_22_2_0, L3C.cp_1_22_2_1, L3C.cp_1_22_2_2⟩
