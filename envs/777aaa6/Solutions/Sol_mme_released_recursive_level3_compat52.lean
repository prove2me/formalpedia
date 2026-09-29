-- Prove2me | solution 1 for mme_released_recursive_level3_compat52
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T12:37:52.57114+00:00
-- url     : https://prove2.me/submissions/b84e1bea-734d-4fdd-99fa-e62fb17bdb7b

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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 4 1 ⟨rr, c⟩ w else 0 := by
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
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 4 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 4 2 ⟨rr, c⟩ w else 0 := by
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


theorem cp_4_23_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (97718386242654753009229283748 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 166684482822711494471578245337830141974387670000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 19322072262205852899907310913784389716051224660000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 166684482822711494471578245337830141974387670000000000000 else 0 := by
    intro v
    rw [hgrp1 (23 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 19655441227851275888850467404460050000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((783688051735342871769 : ℚ)/92412528035000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((45422575965764657128231 : ℚ)/46206264017500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((783688051735342871769 : ℚ)/92412528035000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 46364215001380079867102777217245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 46364215001380079867102777217245000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (23 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 92728430002760159734205554434490000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 14464566792821569781358975884328885000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14464566792821569781358975884328885000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (23 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 28929133585643139562717951768657770000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 353587480965993224272559651903340000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 353587480965993224272559651903340000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 353587480965993224272559651903340000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 353587480965993224272559651903340000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 707174961931986448545119303806680000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 799903391934746608279324858241170000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (23 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 799903391934746608279324858241170000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (403687524102910882752660455990 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 512519624224331262385100032714152905845433400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8904242925481673318590007671870474188309133200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 512519624224331262385100032714152905845433400000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 512519624224331262385100032714152905845433400000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 8904242925481673318590007671870474188309133200000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 512519624224331262385100032714152905845433400000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 9929282173930335843360207737298780000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((5161698653 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((44838301347 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((5161698653 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 327794908069236084746361686550530000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 327794908069236084746361686550530000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 327794908069236084746361686550530000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 327794908069236084746361686550530000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 655589816138472169492723373101060000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (253821643983076104977726521124 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 18280986260859811226933844027796062840090960000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 619027843616752547038855685045467874319818080000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18280986260859811226933844027796062840090960000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 18280986260859811226933844027796062840090960000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 619027843616752547038855685045467874319818080000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 18280986260859811226933844027796062840090960000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 655589816138472169492723373101060000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((6971198229 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((118028801771 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((6971198229 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 46364215001380079867102777217245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46364215001380079867102777217245000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 46364215001380079867102777217245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46364215001380079867102777217245000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 92728430002760159734205554434490000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (180782000746972069681500797294 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 179740665845246717786153029088998455561613140000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 9569800842239842407787901679120783088876773720000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 179740665845246717786153029088998455561613140000000000000 else 0 := by
    intro v
    rw [hgrp2 (23 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 9929282173930335843360207737298780000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((18102080563 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((481897919437 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((18102080563 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 18999851411712803719357744031358990000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 18999851411712803719357744031358990000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (23 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 37999702823425607438715488062717980000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 11292046952000794461398050414206520000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (23 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11292046952000794461398050414206520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (425449677973333461408197839891 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 39236656003321808211456510402895777151076120000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 628701649925342832122206283000888445697847760000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39236656003321808211456510402895777151076120000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 39236656003321808211456510402895777151076120000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 628701649925342832122206283000888445697847760000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 39236656003321808211456510402895777151076120000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 707174961931986448545119303806680000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((55483661209 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((444516338791 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((55483661209 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_23_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 46364215001380079867102777217245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46364215001380079867102777217245000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 46364215001380079867102777217245000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 46364215001380079867102777217245000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 92728430002760159734205554434490000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 179320155158073397289020098918135000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (24 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 179320155158073397289020098918135000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 3475453110385972253877989950540932500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 3475453110385972253877989950540932500000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (24 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6950906220771944507755979901081865000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (352101129766099897574445263821 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 298100476099747042236761475086781420741084325000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6354705268572450423282456950908302158517831350000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 298100476099747042236761475086781420741084325000000000000 else 0 := by
    intro v
    rw [hgrp1 (24 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6950906220771944507755979901081865000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((8361599208296240309597 : ℚ)/194970141319400000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((89123471451403759690403 : ℚ)/97485070659700000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((8361599208296240309597 : ℚ)/194970141319400000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 87321162144829342718235089661870000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87321162144829342718235089661870000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (24 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 174642324289658685436470179323740000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 2338915434207355926274959797197500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2338915434207355926274959797197500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 2338915434207355926274959797197500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 2338915434207355926274959797197500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 4677830868414711852549919594395000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 4677830868414711852549919594395000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 4677830868414711852549919594395000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 4677830868414711852549919594395000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 437583902721606330213948017644510000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 437583902721606330213948017644510000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 437583902721606330213948017644510000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 437583902721606330213948017644510000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 875167805443212660427896035289020000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371078234859373616594725761682 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 279654950128531372321714330991640393235869385000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5516428515071669102684655203809564213528261230000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 279654950128531372321714330991640393235869385000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 279654950128531372321714330991640393235869385000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5516428515071669102684655203809564213528261230000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 279654950128531372321714330991640393235869385000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 6075738415328731847328083865792845000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((46028141933 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((453971858067 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((46028141933 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 87321162144829342718235089661870000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 87321162144829342718235089661870000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 87321162144829342718235089661870000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 87321162144829342718235089661870000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 174642324289658685436470179323740000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 87321162144829342718235089661870000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87321162144829342718235089661870000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 87321162144829342718235089661870000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 87321162144829342718235089661870000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 174642324289658685436470179323740000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5015668334759194559386969716 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 1654722606187339331551499030287098285745210000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 6072428970116357168664980867732270803428509580000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1654722606187339331551499030287098285745210000000000000 else 0 := by
    intro v
    rw [hgrp2 (24 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 6075738415328731847328083865792845000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((136174609 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249863825391 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((136174609 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 437583902721606330213948017644510000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 437583902721606330213948017644510000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (24 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 875167805443212660427896035289020000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_24_2_7 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 4677830868414711852549919594395000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (24 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 4677830868414711852549919594395000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 372718129822002443594900262862944000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 372718129822002443594900262862944000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (25 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 745436259644004887189800525725888000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 19538617600470455446094466692544000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 19538617600470455446094466692544000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 19538617600470455446094466692544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (25356797494773273329506646675 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 43491188516365692378423384545791742011209216000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25169004629964140514982493913953024515977581568000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 43491188516365692378423384545791742011209216000000000000 else 0 := by
    intro v
    rw [hgrp1 (25 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25255987006996871899739340683044608000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((861007501 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((249138992499 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((861007501 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 1954072072324047141148382162268480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1954072072324047141148382162268480000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 1954072072324047141148382162268480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 1954072072324047141148382162268480000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 3908144144648094282296764324536960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 1954072072324047141148382162268480000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 1954072072324047141148382162268480000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (25 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3908144144648094282296764324536960000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (381517866327102221401997820510 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 1207007698829560615102124715922810570174516224000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 22841971609337750669535091251198986859650967552000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1207007698829560615102124715922810570174516224000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 1207007698829560615102124715922810570174516224000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 22841971609337750669535091251198986859650967552000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 1207007698829560615102124715922810570174516224000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 25255987006996871899739340683044608000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((11947738357 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((113052261643 : ℚ)/125000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((11947738357 : ℚ)/250000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 19538617600470455446094466692544000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (25 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 19538617600470455446094466692544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_1_7 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 372718129822002443594900262862944000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 372718129822002443594900262862944000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 372718129822002443594900262862944000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 372718129822002443594900262862944000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) x = 745436259644004887189800525725888000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 372718129822002443594900262862944000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 372718129822002443594900262862944000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 372718129822002443594900262862944000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 372718129822002443594900262862944000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 745436259644004887189800525725888000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 19538617600470455446094466692544000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 19538617600470455446094466692544000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 19538617600470455446094466692544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 14582065575822483091018052503790784000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 14582065575822483091018052503790784000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (25 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 29164131151644966182036105007581568000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 29909567411288971069225905533307456000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (25 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 29909567411288971069225905533307456000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_25_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 9769308800235227723047233346272000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9769308800235227723047233346272000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 9769308800235227723047233346272000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 9769308800235227723047233346272000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 19538617600470455446094466692544000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (210198675842459955416691358513 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 249551625765732067345350274070166726448726080000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 10895903491733819459089753216120018547102547840000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 249551625765732067345350274070166726448726080000000000000 else 0 := by
    intro v
    rw [hgrp1 (26 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 11395006743265283593780453764260352000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((63681063248191475191 : ℚ)/2907799710400000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((1390218791951808524809 : ℚ)/1453899855200000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((63681063248191475191 : ℚ)/2907799710400000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 303405107099171995986790489424832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 303405107099171995986790489424832000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (26 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 606810214198343991973580978849664000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 5482447967937929897604486941220000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 5482447967937929897604486941220000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 5482447967937929897604486941220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 646516556933812729866557638454910000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 646516556933812729866557638454910000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (26 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1293033113867625459733115276909820000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 343111449834640733879767149030078000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 343111449834640733879767149030078000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 343111449834640733879767149030078000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 343111449834640733879767149030078000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 686222899669281467759534298060156000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 5482447967937929897604486941220000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (26 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 5482447967937929897604486941220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_1_6 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (377767747669847280287455636753 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 110162397953179937785221240511155239698700928000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2115857810455942652799664227015257520602598144000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 110162397953179937785221240511155239698700928000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 110162397953179937785221240511155239698700928000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2115857810455942652799664227015257520602598144000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 110162397953179937785221240511155239698700928000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 2336182606362302528370106708037568000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((23577437323 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((226422562677 : ℚ)/250000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((23577437323 : ℚ)/500000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (323244964030878955756732949652 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 89389215795714703354360164185730064724383680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2157404174770873121661386379666107870551232640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 89389215795714703354360164185730064724383680000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 89389215795714703354360164185730064724383680000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 2157404174770873121661386379666107870551232640000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 89389215795714703354360164185730064724383680000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 2336182606362302528370106708037568000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((7652588077 : ℚ)/200000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((92347411923 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((7652588077 : ℚ)/200000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 303405107099171995986790489424832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 303405107099171995986790489424832000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 303405107099171995986790489424832000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 303405107099171995986790489424832000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 606810214198343991973580978849664000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 5482447967937929897604486941220000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 5482447967937929897604486941220000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 5482447967937929897604486941220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 686222899669281467759534298060156000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (26 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 686222899669281467759534298060156000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 4832817175550662528691964017536224000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 4832817175550662528691964017536224000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (26 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 9665634351101325057383928035072448000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 3022405506031583996129641006097724000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (26 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 3022405506031583996129641006097724000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_26_2_6 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (347431026706169216626019278528 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 230952397896298891039295156389073918548620000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5020543172145332115525896628441852162902760000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 230952397896298891039295156389073918548620000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 230952397896298891039295156389073918548620000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 5020543172145332115525896628441852162902760000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 230952397896298891039295156389073918548620000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) x = 5482447967937929897604486941220000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((42125780171 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((457874219829 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((42125780171 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 313934103962692998198541677472686000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 313934103962692998198541677472686000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (27 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 627868207925385996397083354945372000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 25869837979494618428072249869520000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 25869837979494618428072249869520000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 25869837979494618428072249869520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (39756703506851673541138315315 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 3283096643467561307054992336203094763344356000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 1122737000048892701556734410512701810473311288000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 3283096643467561307054992336203094763344356000000000000 else 0 := by
    intro v
    rw [hgrp1 (27 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1129303193335827824170844395185108000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((2907187957 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((497092812043 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((2907187957 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 564651596667913912085422197592554000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 564651596667913912085422197592554000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 564651596667913912085422197592554000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 564651596667913912085422197592554000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 1129303193335827824170844395185108000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 12934918989747309214036124934760000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 12934918989747309214036124934760000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (27 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 25869837979494618428072249869520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_1_5 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (419481272616658491735993638304 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 34163641360033053593195440926244378764133560000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 559540925205319889210692473092883242471732880000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 34163641360033053593195440926244378764133560000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 34163641360033053593195440926244378764133560000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 559540925205319889210692473092883242471732880000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 34163641360033053593195440926244378764133560000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) x = 627868207925385996397083354945372000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((5441212173 : ℚ)/100000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((44558787827 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((5441212173 : ℚ)/100000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 313934103962692998198541677472686000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 313934103962692998198541677472686000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 313934103962692998198541677472686000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 313934103962692998198541677472686000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 627868207925385996397083354945372000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 25869837979494618428072249869520000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 25869837979494618428072249869520000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 25869837979494618428072249869520000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 577586515657661221299458322527314000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 577586515657661221299458322527314000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (27 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1155173031315322442598916645054628000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_27_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 1757171401261213820567927750130480000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (27 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1757171401261213820567927750130480000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (247835840639321223656354447004 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 27467676892400238219024086086284547593381975000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 960919292219184434176184085837430904813236050000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 27467676892400238219024086086284547593381975000000000000 else 0 := by
    intro v
    rw [hgrp1 (28 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 1015854646003984910614232258010000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((8880891026277675607351 : ℚ)/328447667600000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((155342942773722324392649 : ℚ)/164223833800000000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((8880891026277675607351 : ℚ)/328447667600000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 325393013766787743011261925978412500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 325393013766787743011261925978412500000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (28 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 650786027533575486022523851956825000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 15110858513002065460767741990000000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 15110858513002065460767741990000000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 15110858513002065460767741990000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 7555429256501032730383870995000000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 7555429256501032730383870995000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (28 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 15110858513002065460767741990000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_1_4 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 182534309235204712295854203026587500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 182534309235204712295854203026587500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 182534309235204712295854203026587500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 182534309235204712295854203026587500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 365068618470409424591708406053175000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319445732945154506806545714106 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then 13751348346647318004897126787598933168716500000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 337565921777114788581914152477977133662567000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13751348346647318004897126787598933168716500000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 2 then 13751348346647318004897126787598933168716500000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 337565921777114788581914152477977133662567000000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 13751348346647318004897126787598933168716500000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 365068618470409424591708406053175000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 2 then ((1883392279 : ℚ)/50000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((23116607721 : ℚ)/25000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((1883392279 : ℚ)/50000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_1 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 325393013766787743011261925978412500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 325393013766787743011261925978412500000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 325393013766787743011261925978412500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 325393013766787743011261925978412500000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 650786027533575486022523851956825000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_2 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then 15110858513002065460767741990000000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 0 then 15110858513002065460767741990000000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 15110858513002065460767741990000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_3 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then 15110858513002065460767741990000000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (28 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 15110858513002065460767741990000000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 4 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_4 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then 325393013766787743011261925978412500000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 325393013766787743011261925978412500000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (28 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 650786027533575486022523851956825000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_28_2_5 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then 365068618470409424591708406053175000000000000000000000000 else 0 := by
    intro v
    rw [hgrp2 (28 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 365068618470409424591708406053175000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 0 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_29_1_0 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then 42290160779532456205587883923300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42290160779532456205587883923300000000000000000000000000 else 0 := by
    intro v
    rw [hgrp1 (29 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 84580321559064912411175767846600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_29_1_1 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then 26295988363933140263824232153400000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 8 then 26295988363933140263824232153400000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) x = 26295988363933140263824232153400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 8 then (1 : ℚ) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_29_1_2 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (203948766753005282771805438639 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then 554239037330590719214439057322461962686600000000000000 else if 3 * (v 0).val + (v 1).val = 4 then 25187510289271958825395354038755076074626800000000000000 else if 3 * (v 0).val + (v 1).val = 6 then 554239037330590719214439057322461962686600000000000000 else 0 := by
    intro v
    rw [hgrp1 (29 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) v]
    revert v
    decide +kernel
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) x = 26295988363933140263824232153400000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) v = if 3 * (v 0).val + (v 1).val = 2 then ((21076942599 : ℚ)/1000000000000) else if 3 * (v 0).val + (v 1).val = 4 then ((478923057401 : ℚ)/500000000000) else if 3 * (v 0).val + (v 1).val = 6 then ((21076942599 : ℚ)/1000000000000) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_29_1_3 :
    regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then 42290160779532456205587883923300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42290160779532456205587883923300000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 1 ⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 5 then 42290160779532456205587883923300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 7 then 42290160779532456205587883923300000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) x = 84580321559064912411175767846600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩) v = if 3 * (v 0).val + (v 1).val = 5 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 7 then ((1 : ℚ)/2) else 0 := by
    intro v
    unfold freqQ
    rw [hpt, hp v]
    split_ifs <;> norm_num
  unfold regCeilG
  simp only [hW, hf, Fin.sum_univ_four]
  norm_num [qvalQ, logLo, logHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]


theorem cp_4_29_2_0 :
    regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30 := by
  have hp : ∀ v : CompleteSplit.CompleteWord 2, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then 42290160779532456205587883923300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42290160779532456205587883923300000000000000000000000000 else 0 := by
    have hmu : ∀ v : CompleteSplit.CompleteWord 2,
        mu3 4 2 ⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ v = if 3 * (v 0).val + (v 1).val = 1 then 42290160779532456205587883923300000000000000000000000000 else if 3 * (v 0).val + (v 1).val = 3 then 42290160779532456205587883923300000000000000000000000000 else 0 := by decide +kernel
    exact hmu
  have hpt : ∑ x, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) x = 84580321559064912411175767846600000000000000000000000000 := by
    simp only [hp]
    decide +kernel
  have hf : ∀ v : CompleteSplit.CompleteWord 2, freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩) v = if 3 * (v 0).val + (v 1).val = 1 then ((1 : ℚ)/2) else if 3 * (v 0).val + (v 1).val = 3 then ((1 : ℚ)/2) else 0 := by
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
    (regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then -3 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (97718386242654753009229283748 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (403687524102910882752660455990 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (253821643983076104977726521124 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (180782000746972069681500797294 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (425449677973333461408197839891 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (352101129766099897574445263821 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (371078234859373616594725761682 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (5015668334759194559386969716 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (25356797494773273329506646675 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (381517866327102221401997820510 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (210198675842459955416691358513 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (377767747669847280287455636753 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (323244964030878955756732949652 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩, by exact Or.inr rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (347431026706169216626019278528 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (39756703506851673541138315315 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (419481272616658491735993638304 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 5 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (247835840639321223656354447004 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (319445732945154506806545714106 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (7 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (203948766753005282771805438639 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩, by rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) ∧
(regCeilG (freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inl ⟨⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩, by exact Or.inl rfl⟩))
        (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))
      ≤ (693147180559945309417233000006 : ℚ)/10^30) :=
  ⟨L3C.cp_4_23_1_0, L3C.cp_4_23_1_1, L3C.cp_4_23_1_2, L3C.cp_4_23_1_3, L3C.cp_4_23_1_4, L3C.cp_4_23_1_5, L3C.cp_4_23_1_6, L3C.cp_4_23_2_0, L3C.cp_4_23_2_1, L3C.cp_4_23_2_2, L3C.cp_4_23_2_3, L3C.cp_4_23_2_4, L3C.cp_4_23_2_5, L3C.cp_4_23_2_6, L3C.cp_4_24_1_0, L3C.cp_4_24_1_1, L3C.cp_4_24_1_2, L3C.cp_4_24_1_3, L3C.cp_4_24_1_4, L3C.cp_4_24_2_0, L3C.cp_4_24_2_1, L3C.cp_4_24_2_2, L3C.cp_4_24_2_3, L3C.cp_4_24_2_4, L3C.cp_4_24_2_5, L3C.cp_4_24_2_6, L3C.cp_4_24_2_7, L3C.cp_4_25_1_0, L3C.cp_4_25_1_1, L3C.cp_4_25_1_2, L3C.cp_4_25_1_3, L3C.cp_4_25_1_4, L3C.cp_4_25_1_5, L3C.cp_4_25_1_6, L3C.cp_4_25_1_7, L3C.cp_4_25_2_0, L3C.cp_4_25_2_1, L3C.cp_4_25_2_2, L3C.cp_4_25_2_3, L3C.cp_4_25_2_4, L3C.cp_4_26_1_0, L3C.cp_4_26_1_1, L3C.cp_4_26_1_2, L3C.cp_4_26_1_3, L3C.cp_4_26_1_4, L3C.cp_4_26_1_5, L3C.cp_4_26_1_6, L3C.cp_4_26_2_0, L3C.cp_4_26_2_1, L3C.cp_4_26_2_2, L3C.cp_4_26_2_3, L3C.cp_4_26_2_4, L3C.cp_4_26_2_5, L3C.cp_4_26_2_6, L3C.cp_4_27_1_0, L3C.cp_4_27_1_1, L3C.cp_4_27_1_2, L3C.cp_4_27_1_3, L3C.cp_4_27_1_4, L3C.cp_4_27_1_5, L3C.cp_4_27_2_0, L3C.cp_4_27_2_1, L3C.cp_4_27_2_2, L3C.cp_4_27_2_3, L3C.cp_4_28_1_0, L3C.cp_4_28_1_1, L3C.cp_4_28_1_2, L3C.cp_4_28_1_3, L3C.cp_4_28_1_4, L3C.cp_4_28_2_0, L3C.cp_4_28_2_1, L3C.cp_4_28_2_2, L3C.cp_4_28_2_3, L3C.cp_4_28_2_4, L3C.cp_4_28_2_5, L3C.cp_4_29_1_0, L3C.cp_4_29_1_1, L3C.cp_4_29_1_2, L3C.cp_4_29_1_3, L3C.cp_4_29_2_0⟩
