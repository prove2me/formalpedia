-- Prove2me | solution 1 for mme_released_recursive_stage_region0_compat2_s1_h0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T12:54:37.098591+00:00
-- url     : https://prove2.me/submissions/67725cfd-ad6c-4a11-bd15-29f1b443a3f9

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat6
import Theorems.Thm_mme_released_recursive_level3_compat7
import Theorems.Thm_mme_released_recursive_level3_compat8
import Theorems.Thm_mme_released_recursive_level3_compat9
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3K

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



noncomputable abbrev MU := partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)

theorem freq_nonneg (c : _) (w : CompleteSplit.CompleteWord 2) : 0 ≤ freqQ MU c w :=
  (mme_certified_entropy_bridge.{0, 0}.1 MU c w).1

theorem kzero (c : _) (hm : ∑ w, MU c w = 0) :
    ((∑ w, MU c w : ℕ) : ℝ) * entropy (fun w ↦ ((freqQ MU c w : ℚ) : ℝ)) = 0 := by
  rw [hm]; simp

theorem kstep (c : _) (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU c) e ≤ q) (mass : ℕ) (hm : ∑ w, MU c w = mass) :
    ((∑ w, MU c w : ℕ) : ℝ) * entropy (fun w ↦ ((freqQ MU c w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1 (freqQ MU c) (freq_nonneg c) e)
    (by exact_mod_cast h)

theorem kstepC (a : Fin 88) (b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a))
    (hb : yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 0 2 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 0 2 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp44 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ44 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm44_0_2_2 :
    ∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 12307444173162851986252436220352000000000000000000000000 := by
  decide +kernel

theorem cb44_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(44 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((12307444173162851986252436220352000000000000000000000000 * 155386678065370236974286475 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((155386678065370236974286475 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12307444173162851986252436220352000000000000000000000000 cm44_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm44_2_0_2 :
    ∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5406258438548453936073641739812096000000000000000000000000 := by
  decide +kernel

theorem cb44_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(44 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5406258438548453936073641739812096000000000000000000000000 * 335842892740090662716472160358 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then -5 else if k.val = 2 then 7 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((335842892740090662716472160358 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5406258438548453936073641739812096000000000000000000000000 cm44_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm44_3_0_1 :
    ∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1385291257268063014691394107790720000000000000000000000000 := by
  decide +kernel

theorem cb44_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1385291257268063014691394107790720000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1385291257268063014691394107790720000000000000000000000000 cm44_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm44_4_0_0 :
    ∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 12307444173162851986252436220352000000000000000000000000 := by
  decide +kernel

theorem cb44_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((12307444173162851986252436220352000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12307444173162851986252436220352000000000000000000000000 cm44_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6897958384804946700760926185382976000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb44_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6897958384804946700760926185382976000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6897958384804946700760926185382976000000000000000000000000 gm44_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22255419907140049452166248649002624000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb44_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22255419907140049452166248649002624000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22255419907140049452166248649002624000000000000000000000000 gm44_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1491699946256492764687284445570880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb44_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1491699946256492764687284445570880000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1491699946256492764687284445570880000000000000000000000000 gm44_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm44_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg44 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (44 : Fin 88)),
            if yzBoundary 1 (⟨(44 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(44 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(44 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((44 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((44 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((18202147675357008838717619236481001107449659604335674914336409088000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp44 (fun b ↦
    if yzBoundary 1 (⟨(44 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(44 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(44 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ44]
  rw [kzero _ gm44_3]
  rw [kzero _ gm44_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb44_0_2_2 (add_le_add cb44_2_0_2 (add_le_add cb44_3_0_1 (add_le_add cb44_4_0_0 (add_le_add gb44_0 (add_le_add gb44_1 gb44_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp45 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ45 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm45_2_0_2 :
    ∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 148097725648895070946052866583315000000000000000000000000 := by
  decide +kernel

theorem cb45_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((148097725648895070946052866583315000000000000000000000000 * 304693398300090227557287298949 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304693398300090227557287298949 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 148097725648895070946052866583315000000000000000000000000 cm45_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm45_3_0_1 :
    ∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 266903681963249665538409545058134000000000000000000000000 := by
  decide +kernel

theorem cb45_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((266903681963249665538409545058134000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 266903681963249665538409545058134000000000000000000000000 cm45_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm45_4_0_0 :
    ∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 6025222900886436118537588358551000000000000000000000000 := by
  decide +kernel

theorem cb45_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((6025222900886436118537588358551000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6025222900886436118537588358551000000000000000000000000 cm45_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 148097725648895070946052866583315000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((148097725648895070946052866583315000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 148097725648895070946052866583315000000000000000000000000 gm45_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 266903681963249665538409545058134000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((266903681963249665538409545058134000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 266903681963249665538409545058134000000000000000000000000 gm45_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6025222900886436118537588358551000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6025222900886436118537588358551000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6025222900886436118537588358551000000000000000000000000 gm45_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm45_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg45 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (45 : Fin 88)),
            if yzBoundary 1 (⟨(45 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(45 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(45 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((45 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((45 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((415131468576265942473502233043484560618583903075714935908236462000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp45 (fun b ↦
    if yzBoundary 1 (⟨(45 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(45 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(45 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ45]
  rw [kzero _ gm45_3]
  rw [kzero _ gm45_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb45_2_0_2 (add_le_add cb45_3_0_1 (add_le_add cb45_4_0_0 (add_le_add gb45_0 (add_le_add gb45_1 gb45_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp46 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ46 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm46_3_0_1 :
    ∑ w, mu3 0 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84496264492033376183535148731860000000000000000000000000 := by
  decide +kernel

theorem cb46_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84496264492033376183535148731860000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.1 84496264492033376183535148731860000000000000000000000000 cm46_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm46_4_0_0 :
    ∑ w, mu3 0 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25757454141812594476464851268140000000000000000000000000 := by
  decide +kernel

theorem cb46_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25757454141812594476464851268140000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.1 25757454141812594476464851268140000000000000000000000000 cm46_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84496264492033376183535148731860000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb46_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84496264492033376183535148731860000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.1 84496264492033376183535148731860000000000000000000000000 gm46_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25757454141812594476464851268140000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb46_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25757454141812594476464851268140000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.1 25757454141812594476464851268140000000000000000000000000 gm46_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm46_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm46_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg46 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (46 : Fin 88)),
            if yzBoundary 1 (⟨(46 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(46 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(46 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((46 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((46 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76422054217299839712171168487807388158623777618580000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp46 (fun b ↦
    if yzBoundary 1 (⟨(46 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(46 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(46 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ46]
  rw [kzero _ gm46_2]
  rw [kzero _ gm46_3]
  rw [kzero _ gm46_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb46_3_0_1 (add_le_add cb46_4_0_0 (add_le_add gb46_0 gb46_1))) (le_of_eq (by push_cast; ring)))

theorem hsp47 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ47 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm47_0_0_4 :
    ∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25942896862522064876654121101225000000000000000000000000 := by
  decide +kernel

theorem cb47_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25942896862522064876654121101225000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.1 25942896862522064876654121101225000000000000000000000000 cm47_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm47_0_1_3 :
    ∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84703452226319036078345878898775000000000000000000000000 := by
  decide +kernel

theorem cb47_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84703452226319036078345878898775000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.1 84703452226319036078345878898775000000000000000000000000 cm47_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm47_1_0_3 :
    ∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84703452226319036078345878898775000000000000000000000000 := by
  decide +kernel

theorem cb47_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84703452226319036078345878898775000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.1 84703452226319036078345878898775000000000000000000000000 cm47_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm47_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm47_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25942896862522064876654121101225000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb47_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25942896862522064876654121101225000000000000000000000000 * 179531375866933652873901317681 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((179531375866933652873901317681 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.1 25942896862522064876654121101225000000000000000000000000 gm47_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm47_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg47 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (47 : Fin 88)),
            if yzBoundary 1 (⟨(47 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(47 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(47 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((47 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((47 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((122081482156436667425497509339681876993764005349711382827753100000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp47 (fun b ↦
    if yzBoundary 1 (⟨(47 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(47 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(47 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ47]
  rw [kzero _ gm47_0]
  rw [kzero _ gm47_1]
  rw [kzero _ gm47_3]
  rw [kzero _ gm47_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb47_0_0_4 (add_le_add cb47_0_1_3 (add_le_add cb47_1_0_3 gb47_2))) (le_of_eq (by push_cast; ring)))

theorem hsp48 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ48 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm48_0_0_4 :
    ∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 50352354914282163939832069822076000000000000000000000000 := by
  decide +kernel

theorem cb48_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((50352354914282163939832069822076000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 50352354914282163939832069822076000000000000000000000000 cm48_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_0_1_3 :
    ∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2259762406330782596699154171950672000000000000000000000000 := by
  decide +kernel

theorem cb48_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2259762406330782596699154171950672000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2259762406330782596699154171950672000000000000000000000000 cm48_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_0_2_2 :
    ∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1251110091195708296797013758227252000000000000000000000000 := by
  decide +kernel

theorem cb48_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1251110091195708296797013758227252000000000000000000000000 * 414751644479008205844653918488 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((414751644479008205844653918488 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1251110091195708296797013758227252000000000000000000000000 cm48_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_1_0_3 :
    ∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1251110091195708296797013758227252000000000000000000000000 := by
  decide +kernel

theorem cb48_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1251110091195708296797013758227252000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1251110091195708296797013758227252000000000000000000000000 cm48_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm48_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 50352354914282163939832069822076000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb48_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((50352354914282163939832069822076000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 50352354914282163939832069822076000000000000000000000000 gm48_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2259762406330782596699154171950672000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb48_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2259762406330782596699154171950672000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2259762406330782596699154171950672000000000000000000000000 gm48_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm48_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg48 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (48 : Fin 88)),
            if yzBoundary 1 (⟨(48 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(48 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(48 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((48 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((48 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2987352933557031055624828999676885129709792812695244753880644212000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp48 (fun b ↦
    if yzBoundary 1 (⟨(48 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(48 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(48 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ48]
  rw [kzero _ gm48_0]
  rw [kzero _ gm48_3]
  rw [kzero _ gm48_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb48_0_0_4 (add_le_add cb48_0_1_3 (add_le_add cb48_0_2_2 (add_le_add cb48_1_0_3 (add_le_add gb48_1 gb48_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp49 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ49 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm49_0_0_4 :
    ∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 6042968540354413327518722691520000000000000000000000000 := by
  decide +kernel

theorem cb49_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((6042968540354413327518722691520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6042968540354413327518722691520000000000000000000000000 cm49_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_0_1_3 :
    ∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1190931400028066067490581070696640000000000000000000000000 := by
  decide +kernel

theorem cb49_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1190931400028066067490581070696640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1190931400028066067490581070696640000000000000000000000000 cm49_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_0_2_2 :
    ∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 7714190566363488599093298104870880000000000000000000000000 := by
  decide +kernel

theorem cb49_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((7714190566363488599093298104870880000000000000000000000000 * 380580251575718374753858120965 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380580251575718374753858120965 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7714190566363488599093298104870880000000000000000000000000 cm49_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_0_3_1 :
    ∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 230751778887425045608602101740960000000000000000000000000 := by
  decide +kernel

theorem cb49_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((230751778887425045608602101740960000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 230751778887425045608602101740960000000000000000000000000 cm49_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_1_0_3 :
    ∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 230751778887425045608602101740960000000000000000000000000 := by
  decide +kernel

theorem cb49_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((230751778887425045608602101740960000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 230751778887425045608602101740960000000000000000000000000 cm49_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6042968540354413327518722691520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6042968540354413327518722691520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6042968540354413327518722691520000000000000000000000000 gm49_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1190931400028066067490581070696640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1190931400028066067490581070696640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1190931400028066067490581070696640000000000000000000000000 gm49_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7714190566363488599093298104870880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7714190566363488599093298104870880000000000000000000000000 * 10396861359573246658583164103 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10396861359573246658583164103 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7714190566363488599093298104870880000000000000000000000000 gm49_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm49_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg49 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (49 : Fin 88)),
            if yzBoundary 1 (⟨(49 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(49 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(49 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((49 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((49 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4986943330499004819158829449682223160547398551647724559198952320000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp49 (fun b ↦
    if yzBoundary 1 (⟨(49 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(49 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(49 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ49]
  rw [kzero _ gm49_3]
  rw [kzero _ gm49_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb49_0_0_4 (add_le_add cb49_0_1_3 (add_le_add cb49_0_2_2 (add_le_add cb49_0_3_1 (add_le_add cb49_1_0_3 (add_le_add gb49_0 (add_le_add gb49_1 gb49_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp50 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ50 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm50_0_2_2 :
    ∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 361330702763559469025392082933774000000000000000000000000 := by
  decide +kernel

theorem cb50_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((361330702763559469025392082933774000000000000000000000000 * 319511101926457447950130718234 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((319511101926457447950130718234 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 361330702763559469025392082933774000000000000000000000000 cm50_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_0_3_1 :
    ∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 644396640262668098392439161035335000000000000000000000000 := by
  decide +kernel

theorem cb50_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((644396640262668098392439161035335000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 644396640262668098392439161035335000000000000000000000000 cm50_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_0_4_0 :
    ∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 14960723268198291493168756030891000000000000000000000000 := by
  decide +kernel

theorem cb50_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((14960723268198291493168756030891000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14960723268198291493168756030891000000000000000000000000 cm50_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 361330702763559469025392082933774000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((361330702763559469025392082933774000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 361330702763559469025392082933774000000000000000000000000 gm50_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 644396640262668098392439161035335000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((644396640262668098392439161035335000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 644396640262668098392439161035335000000000000000000000000 gm50_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14960723268198291493168756030891000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14960723268198291493168756030891000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14960723268198291493168756030891000000000000000000000000 gm50_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm50_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg50 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (50 : Fin 88)),
            if yzBoundary 1 (⟨(50 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(50 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(50 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((50 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((50 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1008772599720585604967606593265439787052737665340635217683628028000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp50 (fun b ↦
    if yzBoundary 1 (⟨(50 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(50 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(50 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ50]
  rw [kzero _ gm50_3]
  rw [kzero _ gm50_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb50_0_2_2 (add_le_add cb50_0_3_1 (add_le_add cb50_0_4_0 (add_le_add gb50_0 (add_le_add gb50_1 gb50_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp51 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ51 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm51_0_3_1 :
    ∑ w, mu3 0 2 (⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84570789057430738435196083253400000000000000000000000000 := by
  decide +kernel

theorem cb51_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84570789057430738435196083253400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84570789057430738435196083253400000000000000000000000000 cm51_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm51_0_4_0 :
    ∑ w, mu3 0 2 (⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 26301885798817404104803916746600000000000000000000000000 := by
  decide +kernel

theorem cb51_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((26301885798817404104803916746600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26301885798817404104803916746600000000000000000000000000 cm51_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84570789057430738435196083253400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb51_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84570789057430738435196083253400000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84570789057430738435196083253400000000000000000000000000 gm51_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26301885798817404104803916746600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb51_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26301885798817404104803916746600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26301885798817404104803916746600000000000000000000000000 gm51_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm51_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm51_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg51 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (51 : Fin 88)),
            if yzBoundary 1 (⟨(51 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(51 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(51 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((51 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((51 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76851081977747939610137172704974670889523045853020000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp51 (fun b ↦
    if yzBoundary 1 (⟨(51 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(51 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(51 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(51 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(51 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ51]
  rw [kzero _ gm51_2]
  rw [kzero _ gm51_3]
  rw [kzero _ gm51_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb51_0_3_1 (add_le_add cb51_0_4_0 (add_le_add gb51_0 gb51_1))) (le_of_eq (by push_cast; ring)))

theorem hsp52 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ52 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm52_0_0_4 :
    ∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 45104244211418764509356975136238000000000000000000000000 := by
  decide +kernel

theorem cb52_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((45104244211418764509356975136238000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45104244211418764509356975136238000000000000000000000000 cm52_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_0_1_3 :
    ∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1118780234980647741865824586413860000000000000000000000000 := by
  decide +kernel

theorem cb52_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1118780234980647741865824586413860000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1118780234980647741865824586413860000000000000000000000000 cm52_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_1_0_3 :
    ∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2026388240258652729815818438449902000000000000000000000000 := by
  decide +kernel

theorem cb52_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2026388240258652729815818438449902000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2026388240258652729815818438449902000000000000000000000000 cm52_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_2_0_2 :
    ∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1118780234980647741865824586413860000000000000000000000000 := by
  decide +kernel

theorem cb52_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1118780234980647741865824586413860000000000000000000000000 * 414845728425819450195646552378 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((414845728425819450195646552378 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1118780234980647741865824586413860000000000000000000000000 cm52_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm52_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 45104244211418764509356975136238000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb52_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((45104244211418764509356975136238000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45104244211418764509356975136238000000000000000000000000 gm52_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2026388240258652729815818438449902000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb52_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2026388240258652729815818438449902000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2026388240258652729815818438449902000000000000000000000000 gm52_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm52_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg52 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (52 : Fin 88)),
            if yzBoundary 1 (⟨(52 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(52 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(52 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((52 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((52 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2675449742233531695490835698748254007219301129848401675570262060000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp52 (fun b ↦
    if yzBoundary 1 (⟨(52 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(52 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(52 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ52]
  rw [kzero _ gm52_0]
  rw [kzero _ gm52_3]
  rw [kzero _ gm52_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb52_0_0_4 (add_le_add cb52_0_1_3 (add_le_add cb52_1_0_3 (add_le_add cb52_2_0_2 (add_le_add gb52_1 gb52_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp53 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ53 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm53_0_0_4 :
    ∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 7079465060058433606730601005984000000000000000000000000 := by
  decide +kernel

theorem cb53_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((7079465060058433606730601005984000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7079465060058433606730601005984000000000000000000000000 cm53_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_0_1_3 :
    ∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 819711453758798902533419549844832000000000000000000000000 := by
  decide +kernel

theorem cb53_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((819711453758798902533419549844832000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 819711453758798902533419549844832000000000000000000000000 cm53_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_0_2_2 :
    ∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3068005945703459415767569119270944000000000000000000000000 := by
  decide +kernel

theorem cb53_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3068005945703459415767569119270944000000000000000000000000 * 410215198900365192610125367917 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((410215198900365192610125367917 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3068005945703459415767569119270944000000000000000000000000 cm53_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_1_0_3 :
    ∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 826696447047226717311233945610080000000000000000000000000 := by
  decide +kernel

theorem cb53_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((826696447047226717311233945610080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 826696447047226717311233945610080000000000000000000000000 cm53_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_2_0_2 :
    ∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3068005945703459415767569119270944000000000000000000000000 := by
  decide +kernel

theorem cb53_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3068005945703459415767569119270944000000000000000000000000 * 409855693792053264384684342165 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -1 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((409855693792053264384684342165 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3068005945703459415767569119270944000000000000000000000000 cm53_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7079465060058433606730601005984000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7079465060058433606730601005984000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7079465060058433606730601005984000000000000000000000000 gm53_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1646407900806025619844653495454912000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1646407900806025619844653495454912000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1646407900806025619844653495454912000000000000000000000000 gm53_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11789194311704113506426093568536320000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11789194311704113506426093568536320000000000000000000000000 * 53267539441704540028226035297 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 5 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((53267539441704540028226035297 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11789194311704113506426093568536320000000000000000000000000 gm53_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm53_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg53 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (53 : Fin 88)),
            if yzBoundary 1 (⟨(53 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(53 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(53 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((53 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((53 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((5426369736653930680661584919029413814528337817524943404144487168000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp53 (fun b ↦
    if yzBoundary 1 (⟨(53 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(53 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(53 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ53]
  rw [kzero _ gm53_3]
  rw [kzero _ gm53_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb53_0_0_4 (add_le_add cb53_0_1_3 (add_le_add cb53_0_2_2 (add_le_add cb53_1_0_3 (add_le_add cb53_2_0_2 (add_le_add gb53_0 (add_le_add gb53_1 gb53_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp54 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ54 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm54_0_2_2 :
    ∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2325774095928389313570496915996530000000000000000000000000 := by
  decide +kernel

theorem cb54_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2325774095928389313570496915996530000000000000000000000000 * 323300079075674405169197012207 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((323300079075674405169197012207 : ℚ)/10^30) mme_released_recursive_level3_compat7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 2325774095928389313570496915996530000000000000000000000000 cm54_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_0_3_1 :
    ∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 604945373331815342855385301802724000000000000000000000000 := by
  decide +kernel

theorem cb54_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(54 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((604945373331815342855385301802724000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.1 604945373331815342855385301802724000000000000000000000000 cm54_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_0_4_0 :
    ∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5457872328336878237390919047772000000000000000000000000 := by
  decide +kernel

theorem cb54_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5457872328336878237390919047772000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.1 5457872328336878237390919047772000000000000000000000000 cm54_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_2_0_2 :
    ∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5457872328336878237390919047772000000000000000000000000 := by
  decide +kernel

theorem cb54_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5457872328336878237390919047772000000000000000000000000 * 347030490253934188694406476600 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((347030490253934188694406476600 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.1 5457872328336878237390919047772000000000000000000000000 cm54_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3008015842840021724591539416897810000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb54_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3008015842840021724591539416897810000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.1 3008015842840021724591539416897810000000000000000000000000 gm54_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9623329739351469724682754026306112000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb54_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9623329739351469724682754026306112000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.1 9623329739351469724682754026306112000000000000000000000000 gm54_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 682241746911632411021042500901280000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb54_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((682241746911632411021042500901280000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.1 682241746911632411021042500901280000000000000000000000000 gm54_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm54_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg54 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (54 : Fin 88)),
            if yzBoundary 1 (⟨(54 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(54 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(54 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((54 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((54 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((7843517053583525493285087824621767242214432363204842538194357960000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp54 (fun b ↦
    if yzBoundary 1 (⟨(54 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(54 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(54 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ54]
  rw [kzero _ gm54_3]
  rw [kzero _ gm54_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb54_0_2_2 (add_le_add cb54_0_3_1 (add_le_add cb54_0_4_0 (add_le_add cb54_2_0_2 (add_le_add gb54_0 (add_le_add gb54_1 gb54_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp55 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ55 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm55_0_3_1 :
    ∑ w, mu3 0 2 (⟨(55 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 627228167820903674619221236730808000000000000000000000000 := by
  decide +kernel

theorem cb55_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(55 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(55 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((627228167820903674619221236730808000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.1 627228167820903674619221236730808000000000000000000000000 cm55_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm55_0_4_0 :
    ∑ w, mu3 0 2 (⟨(55 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25847229972037833535032879198290000000000000000000000000 := by
  decide +kernel

theorem cb55_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(55 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(55 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25847229972037833535032879198290000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25847229972037833535032879198290000000000000000000000000 cm55_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1754957346722236326945967120801710000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb55_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1754957346722236326945967120801710000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1754957346722236326945967120801710000000000000000000000000 gm55_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1153576408873370485861778763269192000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb55_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1153576408873370485861778763269192000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1153576408873370485861778763269192000000000000000000000000 gm55_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm55_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm55_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg55 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (55 : Fin 88)),
            if yzBoundary 1 (⟨(55 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(55 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(55 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((55 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((55 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1234359671463883026192972572872281683925994637086253000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp55 (fun b ↦
    if yzBoundary 1 (⟨(55 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(55 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(55 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ55]
  rw [kzero _ gm55_2]
  rw [kzero _ gm55_3]
  rw [kzero _ gm55_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb55_0_3_1 (add_le_add cb55_0_4_0 (add_le_add gb55_0 gb55_1))) (le_of_eq (by push_cast; ring)))

theorem hsp56 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ56 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm56_0_0_4 :
    ∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2783685709605199675245782837409000000000000000000000000 := by
  decide +kernel

theorem cb56_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2783685709605199675245782837409000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2783685709605199675245782837409000000000000000000000000 cm56_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_0_1_3 :
    ∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 106174101308546304327508822095432000000000000000000000000 := by
  decide +kernel

theorem cb56_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((106174101308546304327508822095432000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106174101308546304327508822095432000000000000000000000000 cm56_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_1_0_3 :
    ∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 557605166359498558837379781275940000000000000000000000000 := by
  decide +kernel

theorem cb56_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((557605166359498558837379781275940000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 557605166359498558837379781275940000000000000000000000000 cm56_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_2_0_2 :
    ∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3607079735342544153110865613791219000000000000000000000000 := by
  decide +kernel

theorem cb56_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(56 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3607079735342544153110865613791219000000000000000000000000 * 379735420621702414249794419263 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((379735420621702414249794419263 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3607079735342544153110865613791219000000000000000000000000 cm56_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_3_0_1 :
    ∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 106174101308546304327508822095432000000000000000000000000 := by
  decide +kernel

theorem cb56_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(56 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(56 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((106174101308546304327508822095432000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106174101308546304327508822095432000000000000000000000000 cm56_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2783685709605199675245782837409000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb56_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2783685709605199675245782837409000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2783685709605199675245782837409000000000000000000000000 gm56_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 557605166359498558837379781275940000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb56_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((557605166359498558837379781275940000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 557605166359498558837379781275940000000000000000000000000 gm56_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3607079735342544153110865613791219000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb56_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3607079735342544153110865613791219000000000000000000000000 * 10613599556466907198342543803 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10613599556466907198342543803 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3607079735342544153110865613791219000000000000000000000000 gm56_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm56_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg56 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (56 : Fin 88)),
            if yzBoundary 1 (⟨(56 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(56 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(56 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((56 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((56 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2328213496191993544199575127926052119978273574605367340790297644000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp56 (fun b ↦
    if yzBoundary 1 (⟨(56 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(56 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(56 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(56 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(56 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(56 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ56]
  rw [kzero _ gm56_3]
  rw [kzero _ gm56_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb56_0_0_4 (add_le_add cb56_0_1_3 (add_le_add cb56_1_0_3 (add_le_add cb56_2_0_2 (add_le_add cb56_3_0_1 (add_le_add gb56_0 (add_le_add gb56_1 gb56_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp57 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ57 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm57_0_1_3 :
    ∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 85363203105685443353802302925378000000000000000000000000 := by
  decide +kernel

theorem cb57_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(57 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((85363203105685443353802302925378000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85363203105685443353802302925378000000000000000000000000 cm57_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm57_0_2_2 :
    ∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 579427269404626314502027379675226000000000000000000000000 := by
  decide +kernel

theorem cb57_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(57 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((579427269404626314502027379675226000000000000000000000000 * 417205548376556356490455498454 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-50 : Int) else if k.val = 1 then 3 else if k.val = 2 then 8 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((417205548376556356490455498454 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 579427269404626314502027379675226000000000000000000000000 cm57_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm57_1_0_3 :
    ∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 631048163834190450049772362829100000000000000000000000000 := by
  decide +kernel

theorem cb57_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(57 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((631048163834190450049772362829100000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 631048163834190450049772362829100000000000000000000000000 cm57_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm57_2_0_2 :
    ∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 8474570100212276196418299285851064000000000000000000000000 := by
  decide +kernel

theorem cb57_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(57 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((8474570100212276196418299285851064000000000000000000000000 * 433338088699535034889804053281 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((433338088699535034889804053281 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8474570100212276196418299285851064000000000000000000000000 cm57_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm57_3_0_1 :
    ∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 579427269404626314502027379675226000000000000000000000000 := by
  decide +kernel

theorem cb57_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((579427269404626314502027379675226000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 579427269404626314502027379675226000000000000000000000000 cm57_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 716411366939875893403574665754478000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb57_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((716411366939875893403574665754478000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 716411366939875893403574665754478000000000000000000000000 gm57_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 24938180773468721217645397954570296000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb57_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((24938180773468721217645397954570296000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24938180773468721217645397954570296000000000000000000000000 gm57_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 16463610673256445021227098668719232000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb57_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((16463610673256445021227098668719232000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 16463610673256445021227098668719232000000000000000000000000 gm57_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm57_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg57 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (57 : Fin 88)),
            if yzBoundary 1 (⟨(57 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(57 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(57 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((57 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((57 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((22098130870119418888323338706995329277225158516571345590692957558000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp57 (fun b ↦
    if yzBoundary 1 (⟨(57 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(57 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(57 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ57]
  rw [kzero _ gm57_3]
  rw [kzero _ gm57_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb57_0_1_3 (add_le_add cb57_0_2_2 (add_le_add cb57_1_0_3 (add_le_add cb57_2_0_2 (add_le_add cb57_3_0_1 (add_le_add gb57_0 (add_le_add gb57_1 gb57_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp58 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ58 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm58_0_2_2 :
    ∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 602334295450493813547244900260000000000000000000000000000 := by
  decide +kernel

theorem cb58_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(58 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((602334295450493813547244900260000000000000000000000000000 * 254421171457500297303313647084 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -5 else if k.val = 2 then -3 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((254421171457500297303313647084 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 602334295450493813547244900260000000000000000000000000000 cm58_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm58_0_3_1 :
    ∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 85268423117159606847991667836000000000000000000000000000 := by
  decide +kernel

theorem cb58_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((85268423117159606847991667836000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85268423117159606847991667836000000000000000000000000000 cm58_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm58_2_0_2 :
    ∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 653643768476328774856514462428000000000000000000000000000 := by
  decide +kernel

theorem cb58_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((653643768476328774856514462428000000000000000000000000000 * 424747291497541894053616766781 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424747291497541894053616766781 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 653643768476328774856514462428000000000000000000000000000 cm58_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm58_3_0_1 :
    ∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 85268423117159606847991667836000000000000000000000000000 := by
  decide +kernel

theorem cb58_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((85268423117159606847991667836000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85268423117159606847991667836000000000000000000000000000 cm58_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10427261077409330469725436575572000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb58_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10427261077409330469725436575572000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10427261077409330469725436575572000000000000000000000000000 gm58_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 35113157971098379838853143513184000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb58_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((35113157971098379838853143513184000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 35113157971098379838853143513184000000000000000000000000000 gm58_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9171283013482507881321677212884000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb58_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9171283013482507881321677212884000000000000000000000000000 * 180941499135905178566039391377 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 8 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -4 else if k.val = 2 then -7 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((180941499135905178566039391377 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9171283013482507881321677212884000000000000000000000000000 gm58_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm58_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg58 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (58 : Fin 88)),
            if yzBoundary 1 (⟨(58 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(58 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(58 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((58 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((58 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((26547139297153011655055598519902962237031292262286353370869516000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp58 (fun b ↦
    if yzBoundary 1 (⟨(58 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(58 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(58 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ58]
  rw [kzero _ gm58_3]
  rw [kzero _ gm58_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb58_0_2_2 (add_le_add cb58_0_3_1 (add_le_add cb58_2_0_2 (add_le_add cb58_3_0_1 (add_le_add gb58_0 (add_le_add gb58_1 gb58_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp59 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ59 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm59_0_3_1 :
    ∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 751957444167510424652084418709468000000000000000000000000 := by
  decide +kernel

theorem cb59_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((751957444167510424652084418709468000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 751957444167510424652084418709468000000000000000000000000 cm59_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm59_0_4_0 :
    ∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19713878702001233763516657298552000000000000000000000000 := by
  decide +kernel

theorem cb59_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19713878702001233763516657298552000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19713878702001233763516657298552000000000000000000000000 cm59_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm59_3_0_1 :
    ∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19713878702001233763516657298552000000000000000000000000 := by
  decide +kernel

theorem cb59_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19713878702001233763516657298552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (59 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19713878702001233763516657298552000000000000000000000000 cm59_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 30335577704947729675432483342701448000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb59_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((30335577704947729675432483342701448000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 30335577704947729675432483342701448000000000000000000000000 gm59_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29583620260780219250780398923991980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb59_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29583620260780219250780398923991980000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29583620260780219250780398923991980000000000000000000000000 gm59_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm59_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm59_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg59 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (59 : Fin 88)),
            if yzBoundary 1 (⟨(59 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(59 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(59 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((59 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((59 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((21040684776281848225725120762712152128588021169819548000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp59 (fun b ↦
    if yzBoundary 1 (⟨(59 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(59 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(59 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(59 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ59]
  rw [kzero _ gm59_2]
  rw [kzero _ gm59_3]
  rw [kzero _ gm59_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb59_0_3_1 (add_le_add cb59_0_4_0 (add_le_add cb59_3_0_1 (add_le_add gb59_0 gb59_1)))) (le_of_eq (by push_cast; ring)))

theorem hsp60 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ60 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm60_3_0_1 :
    ∑ w, mu3 0 2 (⟨(60 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84624806433168066303665241533078000000000000000000000000 := by
  decide +kernel

theorem cb60_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(60 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(60 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84624806433168066303665241533078000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (60 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84624806433168066303665241533078000000000000000000000000 cm60_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm60_4_0_0 :
    ∑ w, mu3 0 2 (⟨(60 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25061590231107089574334758466922000000000000000000000000 := by
  decide +kernel

theorem cb60_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(60 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(60 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25061590231107089574334758466922000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (60 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25061590231107089574334758466922000000000000000000000000 cm60_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84624806433168066303665241533078000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb60_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84624806433168066303665241533078000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84624806433168066303665241533078000000000000000000000000 gm60_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25061590231107089574334758466922000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb60_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25061590231107089574334758466922000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25061590231107089574334758466922000000000000000000000000 gm60_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm60_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm60_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg60 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (60 : Fin 88)),
            if yzBoundary 1 (⟨(60 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(60 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(60 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((60 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((60 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76028816593622114359935029799981315571081151026414000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp60 (fun b ↦
    if yzBoundary 1 (⟨(60 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(60 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(60 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(60 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(60 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(60 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(60 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ60]
  rw [kzero _ gm60_2]
  rw [kzero _ gm60_3]
  rw [kzero _ gm60_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb60_3_0_1 (add_le_add cb60_4_0_0 (add_le_add gb60_0 gb60_1))) (le_of_eq (by push_cast; ring)))

theorem hsp61 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ61 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm61_0_0_4 :
    ∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 26480238515017457283486329204730000000000000000000000000 := by
  decide +kernel

theorem cb61_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(61 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((26480238515017457283486329204730000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26480238515017457283486329204730000000000000000000000000 cm61_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm61_0_1_3 :
    ∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84887018326516832726513670795270000000000000000000000000 := by
  decide +kernel

theorem cb61_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(61 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84887018326516832726513670795270000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84887018326516832726513670795270000000000000000000000000 cm61_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm61_1_0_3 :
    ∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84887018326516832726513670795270000000000000000000000000 := by
  decide +kernel

theorem cb61_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(61 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(61 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84887018326516832726513670795270000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 84887018326516832726513670795270000000000000000000000000 cm61_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm61_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm61_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26480238515017457283486329204730000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb61_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26480238515017457283486329204730000000000000000000000000 * 203944571693267448535673208038 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((203944571693267448535673208038 : ℚ)/10^30) mme_released_recursive_level3_compat9.1 26480238515017457283486329204730000000000000000000000000 gm61_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm61_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg61 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (61 : Fin 88)),
            if yzBoundary 1 (⟨(61 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(61 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(61 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((61 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((61 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((123078895740611898913638577907282554271149540179462632557596090000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp61 (fun b ↦
    if yzBoundary 1 (⟨(61 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(61 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(61 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(61 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ61]
  rw [kzero _ gm61_0]
  rw [kzero _ gm61_1]
  rw [kzero _ gm61_3]
  rw [kzero _ gm61_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb61_0_0_4 (add_le_add cb61_0_1_3 (add_le_add cb61_1_0_3 gb61_2))) (le_of_eq (by push_cast; ring)))

theorem hsp62 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ62 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm62_0_0_4 :
    ∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 47167491477172161652795691206920000000000000000000000000 := by
  decide +kernel

theorem cb62_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(62 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((47167491477172161652795691206920000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.1 47167491477172161652795691206920000000000000000000000000 cm62_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_0_1_3 :
    ∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2018136379122701727082136459648100000000000000000000000000 := by
  decide +kernel

theorem cb62_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(62 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2018136379122701727082136459648100000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.1 2018136379122701727082136459648100000000000000000000000000 cm62_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_0_2_2 :
    ∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1134716729725808981805067849144980000000000000000000000000 := by
  decide +kernel

theorem cb62_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1134716729725808981805067849144980000000000000000000000000 * 432396614474871667336579430782 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432396614474871667336579430782 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.1 1134716729725808981805067849144980000000000000000000000000 cm62_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_1_0_3 :
    ∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1134716729725808981805067849144980000000000000000000000000 := by
  decide +kernel

theorem cb62_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(62 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(62 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1134716729725808981805067849144980000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.1 1134716729725808981805067849144980000000000000000000000000 cm62_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm62_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 47167491477172161652795691206920000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb62_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((47167491477172161652795691206920000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.1 47167491477172161652795691206920000000000000000000000000 gm62_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2018136379122701727082136459648100000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb62_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2018136379122701727082136459648100000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.1 2018136379122701727082136459648100000000000000000000000000 gm62_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm62_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg62 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (62 : Fin 88)),
            if yzBoundary 1 (⟨(62 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(62 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(62 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((62 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((62 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2708732929170928466022894889063692900379882943274150938848759500000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp62 (fun b ↦
    if yzBoundary 1 (⟨(62 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(62 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(62 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ62]
  rw [kzero _ gm62_0]
  rw [kzero _ gm62_3]
  rw [kzero _ gm62_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb62_0_0_4 (add_le_add cb62_0_1_3 (add_le_add cb62_0_2_2 (add_le_add cb62_1_0_3 (add_le_add gb62_1 gb62_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp63 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ63 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm63_0_0_4 :
    ∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 6976269815207408420085503119816000000000000000000000000 := by
  decide +kernel

theorem cb63_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(63 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((6976269815207408420085503119816000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6976269815207408420085503119816000000000000000000000000 cm63_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_0_1_3 :
    ∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1439950143580930717378684112400784000000000000000000000000 := by
  decide +kernel

theorem cb63_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(63 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1439950143580930717378684112400784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1439950143580930717378684112400784000000000000000000000000 cm63_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_0_2_2 :
    ∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 8898049073826008178307638005329373000000000000000000000000 := by
  decide +kernel

theorem cb63_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((8898049073826008178307638005329373000000000000000000000000 * 383800472505370308044193672659 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((383800472505370308044193672659 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8898049073826008178307638005329373000000000000000000000000 cm63_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_0_3_1 :
    ∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 269913674443606375336592379150027000000000000000000000000 := by
  decide +kernel

theorem cb63_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((269913674443606375336592379150027000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 269913674443606375336592379150027000000000000000000000000 cm63_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_1_0_3 :
    ∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 269913674443606375336592379150027000000000000000000000000 := by
  decide +kernel

theorem cb63_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(63 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(63 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((269913674443606375336592379150027000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 269913674443606375336592379150027000000000000000000000000 cm63_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6976269815207408420085503119816000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6976269815207408420085503119816000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6976269815207408420085503119816000000000000000000000000 gm63_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1439950143580930717378684112400784000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1439950143580930717378684112400784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1439950143580930717378684112400784000000000000000000000000 gm63_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8898049073826008178307638005329373000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8898049073826008178307638005329373000000000000000000000000 * 15884296505572246759807589945 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15884296505572246759807589945 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8898049073826008178307638005329373000000000000000000000000 gm63_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm63_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg63 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (63 : Fin 88)),
            if yzBoundary 1 (⟨(63 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(63 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(63 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((63 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((63 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((5926789257930521977110179369054318192371299642880535539755954448000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp63 (fun b ↦
    if yzBoundary 1 (⟨(63 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(63 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(63 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ63]
  rw [kzero _ gm63_3]
  rw [kzero _ gm63_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb63_0_0_4 (add_le_add cb63_0_1_3 (add_le_add cb63_0_2_2 (add_le_add cb63_0_3_1 (add_le_add cb63_1_0_3 (add_le_add gb63_0 (add_le_add gb63_1 gb63_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp64 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ64 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm64_0_3_1 :
    ∑ w, mu3 0 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84494597806935672487763982184107000000000000000000000000 := by
  decide +kernel

theorem cb64_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84494597806935672487763982184107000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84494597806935672487763982184107000000000000000000000000 cm64_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm64_0_4_0 :
    ∑ w, mu3 0 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25138228372775576563236017815893000000000000000000000000 := by
  decide +kernel

theorem cb64_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25138228372775576563236017815893000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25138228372775576563236017815893000000000000000000000000 cm64_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84494597806935672487763982184107000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb64_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84494597806935672487763982184107000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84494597806935672487763982184107000000000000000000000000 gm64_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25138228372775576563236017815893000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb64_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25138228372775576563236017815893000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25138228372775576563236017815893000000000000000000000000 gm64_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm64_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm64_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg64 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (64 : Fin 88)),
            if yzBoundary 1 (⟨(64 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(64 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(64 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((64 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((64 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((75991684363285412271462464027502842074632129237663000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp64 (fun b ↦
    if yzBoundary 1 (⟨(64 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(64 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(64 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ64]
  rw [kzero _ gm64_2]
  rw [kzero _ gm64_3]
  rw [kzero _ gm64_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb64_0_3_1 (add_le_add cb64_0_4_0 (add_le_add gb64_0 gb64_1))) (le_of_eq (by push_cast; ring)))

theorem hsp65 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ65 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm65_0_0_4 :
    ∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 41182271337735574882036208676309000000000000000000000000 := by
  decide +kernel

theorem cb65_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(65 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((41182271337735574882036208676309000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 41182271337735574882036208676309000000000000000000000000 cm65_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_0_1_3 :
    ∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 991519318606117943580620010007041000000000000000000000000 := by
  decide +kernel

theorem cb65_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((991519318606117943580620010007041000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 991519318606117943580620010007041000000000000000000000000 cm65_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_1_0_3 :
    ∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1770057894734789253544343781316650000000000000000000000000 := by
  decide +kernel

theorem cb65_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1770057894734789253544343781316650000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1770057894734789253544343781316650000000000000000000000000 cm65_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_2_0_2 :
    ∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 991519318606117943580620010007041000000000000000000000000 := by
  decide +kernel

theorem cb65_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((991519318606117943580620010007041000000000000000000000000 * 432783914648317144086949380894 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (22 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432783914648317144086949380894 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 991519318606117943580620010007041000000000000000000000000 cm65_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm65_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 41182271337735574882036208676309000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb65_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((41182271337735574882036208676309000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 41182271337735574882036208676309000000000000000000000000 gm65_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1770057894734789253544343781316650000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb65_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1770057894734789253544343781316650000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1770057894734789253544343781316650000000000000000000000000 gm65_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm65_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg65 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (65 : Fin 88)),
            if yzBoundary 1 (⟨(65 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(65 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(65 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((65 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((65 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2371838446748434191428710470516645323336945733888710959460825367000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp65 (fun b ↦
    if yzBoundary 1 (⟨(65 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(65 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(65 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ65]
  rw [kzero _ gm65_0]
  rw [kzero _ gm65_3]
  rw [kzero _ gm65_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb65_0_0_4 (add_le_add cb65_0_1_3 (add_le_add cb65_1_0_3 (add_le_add cb65_2_0_2 (add_le_add gb65_1 gb65_2))))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((128352027300289927976731127295859133320135885977350297754720637005000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg44 (add_le_add L3K.reg45 (add_le_add L3K.reg46 (add_le_add L3K.reg47 (add_le_add L3K.reg48 (add_le_add L3K.reg49 (add_le_add L3K.reg50 (add_le_add L3K.reg51 (add_le_add L3K.reg52 (add_le_add L3K.reg53 (add_le_add L3K.reg54 (add_le_add L3K.reg55 (add_le_add L3K.reg56 (add_le_add L3K.reg57 (add_le_add L3K.reg58 (add_le_add L3K.reg59 (add_le_add L3K.reg60 (add_le_add L3K.reg61 (add_le_add L3K.reg62 (add_le_add L3K.reg63 (add_le_add L3K.reg64 L3K.reg65))))))))))))))))))))) (le_of_eq (by push_cast; ring))
