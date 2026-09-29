-- Prove2me | solution 1 for mme_released_recursive_stage_region5_compat2_s1_h0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T15:09:18.859989+00:00
-- url     : https://prove2.me/submissions/7c75e40a-07ee-477e-9bd0-0e5e237b25c3

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat66
import Theorems.Thm_mme_released_recursive_level3_compat67
import Theorems.Thm_mme_released_recursive_level3_compat68
import Theorems.Thm_mme_released_recursive_level3_compat69
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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

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



noncomputable abbrev MU := partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)

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

theorem kstepC (a : Fin 88) (b : Split (2 * 2 ^ (2 - 1)) (parent3 5 a))
    (hb : yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 5 2 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 5 2 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp44 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ44 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm44_0_3_1 :
    ∑ w, mu3 5 2 (⟨(44 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84570757258322306234637780358290000000000000000000000000 := by
  decide +kernel

theorem cb44_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(44 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(44 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84570757258322306234637780358290000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat66.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84570757258322306234637780358290000000000000000000000000 cm44_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm44_0_4_0 :
    ∑ w, mu3 5 2 (⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 26301812160048147435362219641710000000000000000000000000 := by
  decide +kernel

theorem cb44_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((26301812160048147435362219641710000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (44 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat66.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26301812160048147435362219641710000000000000000000000000 cm44_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84570757258322306234637780358290000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb44_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84570757258322306234637780358290000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((44 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat66.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84570757258322306234637780358290000000000000000000000000 gm44_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26301812160048147435362219641710000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb44_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26301812160048147435362219641710000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((44 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat66.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26301812160048147435362219641710000000000000000000000000 gm44_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm44_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm44_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm44_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(44 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (44 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg44 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (44 : Fin 88)),
            if yzBoundary 1 (⟨(44 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(44 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(44 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((44 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((44 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76851008893780295345534239314294636928533925897710000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp44 (fun b ↦
    if yzBoundary 1 (⟨(44 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(44 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(44 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(44 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(44 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ44]
  rw [kzero _ gm44_2]
  rw [kzero _ gm44_3]
  rw [kzero _ gm44_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb44_0_3_1 (add_le_add cb44_0_4_0 (add_le_add gb44_0 gb44_1))) (le_of_eq (by push_cast; ring)))

theorem hsp45 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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
    ∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 136808072466200730735220419011673000000000000000000000000 := by
  decide +kernel

theorem cb45_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((136808072466200730735220419011673000000000000000000000000 * 304601814907823416144309485820 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304601814907823416144309485820 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.1 136808072466200730735220419011673000000000000000000000000 cm45_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm45_3_0_1 :
    ∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 246570440250177822188000306361646000000000000000000000000 := by
  decide +kernel

theorem cb45_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((246570440250177822188000306361646000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.1 246570440250177822188000306361646000000000000000000000000 cm45_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm45_4_0_0 :
    ∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5563611127790595329779274626681000000000000000000000000 := by
  decide +kernel

theorem cb45_4_0_0 :
    ((∑ w, mu3 5 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5563611127790595329779274626681000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (45 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.1 5563611127790595329779274626681000000000000000000000000 cm45_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 136808072466200730735220419011673000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((136808072466200730735220419011673000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.1 136808072466200730735220419011673000000000000000000000000 gm45_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 246570440250177822188000306361646000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((246570440250177822188000306361646000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.1 246570440250177822188000306361646000000000000000000000000 gm45_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5563611127790595329779274626681000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb45_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5563611127790595329779274626681000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((45 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.1 5563611127790595329779274626681000000000000000000000000 gm45_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm45_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm45_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(45 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (45 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg45 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (45 : Fin 88)),
            if yzBoundary 1 (⟨(45 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(45 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(45 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((45 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((45 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((383491198104916194786824337117397426364337797368532230698171857000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp45 (fun b ↦
    if yzBoundary 1 (⟨(45 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(45 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(45 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(45 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(45 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [hJ45]
  rw [kzero _ gm45_3]
  rw [kzero _ gm45_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb45_2_0_2 (add_le_add cb45_3_0_1 (add_le_add cb45_4_0_0 (add_le_add gb45_0 (add_le_add gb45_1 gb45_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp46 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ46 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm46_0_2_2 :
    ∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 11937625775181041168799700224116000000000000000000000000 := by
  decide +kernel

theorem cb46_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((11937625775181041168799700224116000000000000000000000000 * 180064988714061456575081263 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 8 else if k.val = 2 then -8 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((180064988714061456575081263 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11937625775181041168799700224116000000000000000000000000 cm46_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm46_2_0_2 :
    ∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5240457383253868234648139466532198000000000000000000000000 := by
  decide +kernel

theorem cb46_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(46 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5240457383253868234648139466532198000000000000000000000000 * 335826751111712028023367829072 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 3 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((335826751111712028023367829072 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5240457383253868234648139466532198000000000000000000000000 cm46_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm46_3_0_1 :
    ∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1343049277833247086610442914083650000000000000000000000000 := by
  decide +kernel

theorem cb46_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1343049277833247086610442914083650000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1343049277833247086610442914083650000000000000000000000000 cm46_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm46_4_0_0 :
    ∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 11937625775181041168799700224116000000000000000000000000 := by
  decide +kernel

theorem cb46_4_0_0 :
    ((∑ w, mu3 5 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((11937625775181041168799700224116000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (46 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11937625775181041168799700224116000000000000000000000000 cm46_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6686288329393332117942333769738208000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb46_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6686288329393332117942333769738208000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((46 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6686288329393332117942333769738208000000000000000000000000 gm46_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21573376833632905279835290145991702000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb46_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21573376833632905279835290145991702000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((46 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21573376833632905279835290145991702000000000000000000000000 gm46_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1445830946139463883294194303206010000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb46_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1445830946139463883294194303206010000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((46 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1445830946139463883294194303206010000000000000000000000000 gm46_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm46_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm46_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(46 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (46 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg46 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (46 : Fin 88)),
            if yzBoundary 1 (⟨(46 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(46 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(46 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((46 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((46 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17644344074579055468114895077854907627769663923393056503249429214000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp46 (fun b ↦
    if yzBoundary 1 (⟨(46 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(46 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(46 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(46 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(46 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [hJ46]
  rw [kzero _ gm46_3]
  rw [kzero _ gm46_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb46_0_2_2 (add_le_add cb46_2_0_2 (add_le_add cb46_3_0_1 (add_le_add cb46_4_0_0 (add_le_add gb46_0 (add_le_add gb46_1 gb46_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp47 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ47 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm47_0_2_2 :
    ∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 650591108983478596234176098383800000000000000000000000000 := by
  decide +kernel

theorem cb47_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((650591108983478596234176098383800000000000000000000000000 * 253822381089061327344199564543 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((253822381089061327344199564543 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 650591108983478596234176098383800000000000000000000000000 cm47_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm47_0_3_1 :
    ∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 92013122202340833896332277974800000000000000000000000000 := by
  decide +kernel

theorem cb47_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((92013122202340833896332277974800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92013122202340833896332277974800000000000000000000000000 cm47_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm47_2_0_2 :
    ∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 701771726799808752908908818055800000000000000000000000000 := by
  decide +kernel

theorem cb47_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(47 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((701771726799808752908908818055800000000000000000000000000 * 425448009091265759127873866677 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((425448009091265759127873866677 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 701771726799808752908908818055800000000000000000000000000 cm47_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm47_3_0_1 :
    ∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 92013122202340833896332277974800000000000000000000000000 := by
  decide +kernel

theorem cb47_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(47 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(47 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((92013122202340833896332277974800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (47 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92013122202340833896332277974800000000000000000000000000 cm47_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11206526597115447489405919415025000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb47_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11206526597115447489405919415025000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((47 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11206526597115447489405919415025000000000000000000000000000 gm47_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37711711768757721356195496614000400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb47_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37711711768757721356195496614000400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((47 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37711711768757721356195496614000400000000000000000000000000 gm47_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9854163761332160140262834498585400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb47_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9854163761332160140262834498585400000000000000000000000000 * 180786266867131135744252402089 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((47 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((180786266867131135744252402089 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9854163761332160140262834498585400000000000000000000000000 gm47_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm47_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm47_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(47 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (47 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg47 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (47 : Fin 88)),
            if yzBoundary 1 (⟨(47 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(47 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(47 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((47 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((47 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((28512523406971549756691282125743865955494771849853060281061955600000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp47 (fun b ↦
    if yzBoundary 1 (⟨(47 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(47 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(47 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(47 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(47 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ47]
  rw [kzero _ gm47_3]
  rw [kzero _ gm47_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb47_0_2_2 (add_le_add cb47_0_3_1 (add_le_add cb47_2_0_2 (add_le_add cb47_3_0_1 (add_le_add gb47_0 (add_le_add gb47_1 gb47_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp48 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ48 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm48_0_2_2 :
    ∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2412099486689945220850257411187437000000000000000000000000 := by
  decide +kernel

theorem cb48_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2412099486689945220850257411187437000000000000000000000000 * 323244185686231948448181363544 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((323244185686231948448181363544 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2412099486689945220850257411187437000000000000000000000000 cm48_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_0_3_1 :
    ∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 626507488512650170344026970219249000000000000000000000000 := by
  decide +kernel

theorem cb48_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(48 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((626507488512650170344026970219249000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 626507488512650170344026970219249000000000000000000000000 cm48_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_0_4_0 :
    ∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5659588881299599921141271833554000000000000000000000000 := by
  decide +kernel

theorem cb48_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(48 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5659588881299599921141271833554000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5659588881299599921141271833554000000000000000000000000 cm48_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm48_2_0_2 :
    ∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5659588881299599921141271833554000000000000000000000000 := by
  decide +kernel

theorem cb48_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(48 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(48 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5659588881299599921141271833554000000000000000000000000 * 347409290173752475846231060658 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (48 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((347409290173752475846231060658 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5659588881299599921141271833554000000000000000000000000 cm48_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3120553584411712781264371105409547000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb48_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3120553584411712781264371105409547000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((48 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3120553584411712781264371105409547000000000000000000000000 gm48_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9979576151241156786166948275294549000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb48_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9979576151241156786166948275294549000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((48 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9979576151241156786166948275294549000000000000000000000000 gm48_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 708454097721767560414113694222110000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb48_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((708454097721767560414113694222110000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((48 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 708454097721767560414113694222110000000000000000000000000 gm48_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm48_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm48_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(48 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (48 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg48 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (48 : Fin 88)),
            if yzBoundary 1 (⟨(48 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(48 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(48 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((48 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((48 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((8133240299803510948613734379650911562496682219209674211583654525000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp48 (fun b ↦
    if yzBoundary 1 (⟨(48 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(48 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(48 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(48 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(48 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ48]
  rw [kzero _ gm48_3]
  rw [kzero _ gm48_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb48_0_2_2 (add_le_add cb48_0_3_1 (add_le_add cb48_0_4_0 (add_le_add cb48_2_0_2 (add_le_add gb48_0 (add_le_add gb48_1 gb48_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp49 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ49 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm49_0_2_2 :
    ∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 360400380100754606073625739459456000000000000000000000000 := by
  decide +kernel

theorem cb49_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((360400380100754606073625739459456000000000000000000000000 * 319447369004443125013528638442 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((319447369004443125013528638442 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360400380100754606073625739459456000000000000000000000000 cm49_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_0_3_1 :
    ∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 642492417530129707345430598622208000000000000000000000000 := by
  decide +kernel

theorem cb49_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((642492417530129707345430598622208000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 642492417530129707345430598622208000000000000000000000000 cm49_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm49_0_4_0 :
    ∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 14918445546805437812943661918336000000000000000000000000 := by
  decide +kernel

theorem cb49_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((14918445546805437812943661918336000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (49 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14918445546805437812943661918336000000000000000000000000 cm49_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 360400380100754606073625739459456000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((360400380100754606073625739459456000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360400380100754606073625739459456000000000000000000000000 gm49_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 642492417530129707345430598622208000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((642492417530129707345430598622208000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 642492417530129707345430598622208000000000000000000000000 gm49_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14918445546805437812943661918336000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb49_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14918445546805437812943661918336000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((49 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14918445546805437812943661918336000000000000000000000000 gm49_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm49_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm49_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(49 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (49 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg49 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (49 : Fin 88)),
            if yzBoundary 1 (⟨(49 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(49 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(49 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((49 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((49 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1005812568695692492194252134424618980324284685715637052296546944000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp49 (fun b ↦
    if yzBoundary 1 (⟨(49 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(49 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(49 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(49 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(49 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ49]
  rw [kzero _ gm49_3]
  rw [kzero _ gm49_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb49_0_2_2 (add_le_add cb49_0_3_1 (add_le_add cb49_0_4_0 (add_le_add gb49_0 (add_le_add gb49_1 gb49_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp50 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ50 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm50_0_1_3 :
    ∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 105494354096485089085448829236100000000000000000000000000 := by
  decide +kernel

theorem cb50_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((105494354096485089085448829236100000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 105494354096485089085448829236100000000000000000000000000 cm50_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_0_2_2 :
    ∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 720906590839023819958713557761890000000000000000000000000 := by
  decide +kernel

theorem cb50_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((720906590839023819958713557761890000000000000000000000000 * 416574310596470187456888180654 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416574310596470187456888180654 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 720906590839023819958713557761890000000000000000000000000 cm50_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_1_0_3 :
    ∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 775063121719317348615084770327370000000000000000000000000 := by
  decide +kernel

theorem cb50_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((775063121719317348615084770327370000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 775063121719317348615084770327370000000000000000000000000 cm50_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_2_0_2 :
    ∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 10478067948709447334960162702888370000000000000000000000000 := by
  decide +kernel

theorem cb50_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((10478067948709447334960162702888370000000000000000000000000 * 433329095893823217303625121216 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((433329095893823217303625121216 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10478067948709447334960162702888370000000000000000000000000 cm50_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm50_3_0_1 :
    ∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 720906590839023819958713557761890000000000000000000000000 := by
  decide +kernel

theorem cb50_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((720906590839023819958713557761890000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (50 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 720906590839023819958713557761890000000000000000000000000 cm50_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 880557475815802437700533599563470000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((880557475815802437700533599563470000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 880557475815802437700533599563470000000000000000000000000 gm50_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 30835218222964432861550752842674640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((30835218222964432861550752842674640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 30835218222964432861550752842674640000000000000000000000000 gm50_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20357150274254985526590590139786270000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb50_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20357150274254985526590590139786270000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((50 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 20357150274254985526590590139786270000000000000000000000000 gm50_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm50_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm50_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(50 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (50 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg50 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (50 : Fin 88)),
            if yzBoundary 1 (⟨(50 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(50 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(50 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((50 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((50 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27324157752779830428198480215413490399479328341520734862978582160000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp50 (fun b ↦
    if yzBoundary 1 (⟨(50 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(50 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(50 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(50 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(50 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ50]
  rw [kzero _ gm50_3]
  rw [kzero _ gm50_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb50_0_1_3 (add_le_add cb50_0_2_2 (add_le_add cb50_1_0_3 (add_le_add cb50_2_0_2 (add_le_add cb50_3_0_1 (add_le_add gb50_0 (add_le_add gb50_1 gb50_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp51 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ51 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm51_0_0_4 :
    ∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 498763013731396077323731987600000000000000000000000000 := by
  decide +kernel

theorem cb51_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((498763013731396077323731987600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 498763013731396077323731987600000000000000000000000000 cm51_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm51_0_1_3 :
    ∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 18574360855214534163748695450040000000000000000000000000 := by
  decide +kernel

theorem cb51_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((18574360855214534163748695450040000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18574360855214534163748695450040000000000000000000000000 cm51_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm51_1_0_3 :
    ∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 94921297300518680067710907911680000000000000000000000000 := by
  decide +kernel

theorem cb51_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((94921297300518680067710907911680000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 94921297300518680067710907911680000000000000000000000000 cm51_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm51_2_0_2 :
    ∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 657041464805096271011216664650680000000000000000000000000 := by
  decide +kernel

theorem cb51_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((657041464805096271011216664650680000000000000000000000000 * 370677481646994974137499726462 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370677481646994974137499726462 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 657041464805096271011216664650680000000000000000000000000 cm51_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm51_3_0_1 :
    ∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 18574360855214534163748695450040000000000000000000000000 := by
  decide +kernel

theorem cb51_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((18574360855214534163748695450040000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (51 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.1 18574360855214534163748695450040000000000000000000000000 cm51_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 498763013731396077323731987600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb51_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((498763013731396077323731987600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((51 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.1 498763013731396077323731987600000000000000000000000000 gm51_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 94921297300518680067710907911680000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb51_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((94921297300518680067710907911680000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((51 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.1 94921297300518680067710907911680000000000000000000000000 gm51_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 657041464805096271011216664650680000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb51_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((657041464805096271011216664650680000000000000000000000000 * 5078282555657284181309391428 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((51 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -5 else if k.val = 2 then 2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5078282555657284181309391428 : ℚ)/10^30) mme_released_recursive_level3_compat67.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 657041464805096271011216664650680000000000000000000000000 gm51_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm51_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm51_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(51 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (51 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg51 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (51 : Fin 88)),
            if yzBoundary 1 (⟨(51 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(51 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(51 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((51 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((51 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((404225508633552676460015129551753448952745142226052324796832240000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp51 (fun b ↦
    if yzBoundary 1 (⟨(51 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(51 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(51 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(51 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(51 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(51 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(51 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ51]
  rw [kzero _ gm51_3]
  rw [kzero _ gm51_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb51_0_0_4 (add_le_add cb51_0_1_3 (add_le_add cb51_1_0_3 (add_le_add cb51_2_0_2 (add_le_add cb51_3_0_1 (add_le_add gb51_0 (add_le_add gb51_1 gb51_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp52 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 22427966403115820596943672672250000000000000000000000000 := by
  decide +kernel

theorem cb52_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((22427966403115820596943672672250000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.1 22427966403115820596943672672250000000000000000000000000 cm52_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_0_1_3 :
    ∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2546636428074129845398346021334750000000000000000000000000 := by
  decide +kernel

theorem cb52_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2546636428074129845398346021334750000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.1 2546636428074129845398346021334750000000000000000000000000 cm52_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_0_2_2 :
    ∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 10293886767204650957777049818961000000000000000000000000000 := by
  decide +kernel

theorem cb52_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((10293886767204650957777049818961000000000000000000000000000 * 408038604367546829727663627813 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((408038604367546829727663627813 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.1 10293886767204650957777049818961000000000000000000000000000 cm52_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_1_0_3 :
    ∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2572855676873132726168013794438250000000000000000000000000 := by
  decide +kernel

theorem cb52_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2572855676873132726168013794438250000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.1 2572855676873132726168013794438250000000000000000000000000 cm52_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm52_2_0_2 :
    ∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 10293886767204650957777049818961000000000000000000000000000 := by
  decide +kernel

theorem cb52_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((10293886767204650957777049818961000000000000000000000000000 * 407817403571256462325670408748 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (52 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((407817403571256462325670408748 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10293886767204650957777049818961000000000000000000000000000 cm52_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22427966403115820596943672672250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb52_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22427966403115820596943672672250000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((52 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22427966403115820596943672672250000000000000000000000000 gm52_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5119492104947262571566359815773000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb52_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5119492104947262571566359815773000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((52 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.1 5119492104947262571566359815773000000000000000000000000000 gm52_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 39284394017771236595619293385187500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb52_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((39284394017771236595619293385187500000000000000000000000000 * 23191703510138847996642413306 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((52 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((23191703510138847996642413306 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.1 39284394017771236595619293385187500000000000000000000000000 gm52_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm52_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm52_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(52 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (52 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg52 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (52 : Fin 88)),
            if yzBoundary 1 (⟨(52 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(52 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(52 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((52 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((52 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((16406524419587471998786124926579547208853705877873382385544683500000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp52 (fun b ↦
    if yzBoundary 1 (⟨(52 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(52 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(52 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(52 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(52 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ52]
  rw [kzero _ gm52_3]
  rw [kzero _ gm52_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb52_0_0_4 (add_le_add cb52_0_1_3 (add_le_add cb52_0_2_2 (add_le_add cb52_1_0_3 (add_le_add cb52_2_0_2 (add_le_add gb52_0 (add_le_add gb52_1 gb52_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp53 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 4692038947879554628174331018208000000000000000000000000 := by
  decide +kernel

theorem cb53_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((4692038947879554628174331018208000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4692038947879554628174331018208000000000000000000000000 cm53_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_0_1_3 :
    ∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 877359304420705526108920869227040000000000000000000000000 := by
  decide +kernel

theorem cb53_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((877359304420705526108920869227040000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 877359304420705526108920869227040000000000000000000000000 cm53_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_0_2_2 :
    ∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 6091572323801452556605002526578240000000000000000000000000 := by
  decide +kernel

theorem cb53_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((6091572323801452556605002526578240000000000000000000000000 * 371116721901530093380889409851 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((371116721901530093380889409851 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6091572323801452556605002526578240000000000000000000000000 cm53_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_0_3_1 :
    ∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 175077156034049519769902273176512000000000000000000000000 := by
  decide +kernel

theorem cb53_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((175077156034049519769902273176512000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 175077156034049519769902273176512000000000000000000000000 cm53_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm53_1_0_3 :
    ∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 175077156034049519769902273176512000000000000000000000000 := by
  decide +kernel

theorem cb53_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((175077156034049519769902273176512000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (53 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 175077156034049519769902273176512000000000000000000000000 cm53_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4692038947879554628174331018208000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4692038947879554628174331018208000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4692038947879554628174331018208000000000000000000000000 gm53_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 877359304420705526108920869227040000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((877359304420705526108920869227040000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 877359304420705526108920869227040000000000000000000000000 gm53_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6091572323801452556605002526578240000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb53_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6091572323801452556605002526578240000000000000000000000000 * 5021375724162620841053885019 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((53 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5021375724162620841053885019 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6091572323801452556605002526578240000000000000000000000000 gm53_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm53_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm53_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(53 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (53 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg53 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (53 : Fin 88)),
            if yzBoundary 1 (⟨(53 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(53 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(53 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((53 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((53 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3750259155989402265901776109337057809956556822156208074020726336000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp53 (fun b ↦
    if yzBoundary 1 (⟨(53 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(53 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(53 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(53 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ53]
  rw [kzero _ gm53_3]
  rw [kzero _ gm53_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb53_0_0_4 (add_le_add cb53_0_1_3 (add_le_add cb53_0_2_2 (add_le_add cb53_0_3_1 (add_le_add cb53_1_0_3 (add_le_add gb53_0 (add_le_add gb53_1 gb53_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp54 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ54 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm54_0_0_4 :
    ∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 45755483389312062770756600692112000000000000000000000000 := by
  decide +kernel

theorem cb54_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((45755483389312062770756600692112000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45755483389312062770756600692112000000000000000000000000 cm54_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_0_1_3 :
    ∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1194143550849303583706670349985692000000000000000000000000 := by
  decide +kernel

theorem cb54_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1194143550849303583706670349985692000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1194143550849303583706670349985692000000000000000000000000 cm54_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_1_0_3 :
    ∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2221898377015309192550573049322196000000000000000000000000 := by
  decide +kernel

theorem cb54_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2221898377015309192550573049322196000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2221898377015309192550573049322196000000000000000000000000 cm54_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm54_2_0_2 :
    ∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1194143550849303583706670349985692000000000000000000000000 := by
  decide +kernel

theorem cb54_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1194143550849303583706670349985692000000000000000000000000 * 380502567739227767315528583298 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (54 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380502567739227767315528583298 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1194143550849303583706670349985692000000000000000000000000 cm54_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm54_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 45755483389312062770756600692112000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb54_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((45755483389312062770756600692112000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((54 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45755483389312062770756600692112000000000000000000000000 gm54_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2221898377015309192550573049322196000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb54_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2221898377015309192550573049322196000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((54 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2221898377015309192550573049322196000000000000000000000000 gm54_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm54_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm54_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(54 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (54 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg54 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (54 : Fin 88)),
            if yzBoundary 1 (⟨(54 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(54 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(54 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((54 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((54 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2853909802627774603399822789553509613057801052054868538880272372000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp54 (fun b ↦
    if yzBoundary 1 (⟨(54 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(54 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(54 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(54 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(54 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ54]
  rw [kzero _ gm54_0]
  rw [kzero _ gm54_3]
  rw [kzero _ gm54_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb54_0_0_4 (add_le_add cb54_0_1_3 (add_le_add cb54_1_0_3 (add_le_add cb54_2_0_2 (add_le_add gb54_1 gb54_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp55 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
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

theorem cm55_0_0_4 :
    ∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 50962100981824188209951855899785000000000000000000000000 := by
  decide +kernel

theorem cb55_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((50962100981824188209951855899785000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 50962100981824188209951855899785000000000000000000000000 cm55_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm55_0_1_3 :
    ∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2479949450212390972946628599541420000000000000000000000000 := by
  decide +kernel

theorem cb55_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2479949450212390972946628599541420000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2479949450212390972946628599541420000000000000000000000000 cm55_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm55_0_2_2 :
    ∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1337392590664624559646419544558795000000000000000000000000 := by
  decide +kernel

theorem cb55_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1337392590664624559646419544558795000000000000000000000000 * 380293673832837776842573244932 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380293673832837776842573244932 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1337392590664624559646419544558795000000000000000000000000 cm55_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm55_1_0_3 :
    ∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1337392590664624559646419544558795000000000000000000000000 := by
  decide +kernel

theorem cb55_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1337392590664624559646419544558795000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (55 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1337392590664624559646419544558795000000000000000000000000 cm55_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm55_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 50962100981824188209951855899785000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb55_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((50962100981824188209951855899785000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((55 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 50962100981824188209951855899785000000000000000000000000 gm55_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2479949450212390972946628599541420000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb55_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2479949450212390972946628599541420000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((55 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2479949450212390972946628599541420000000000000000000000000 gm55_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm55_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm55_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(55 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (55 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg55 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (55 : Fin 88)),
            if yzBoundary 1 (⟨(55 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(55 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(55 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((55 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((55 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3189906051138480127108498734342086482686410670727203530597865375000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp55 (fun b ↦
    if yzBoundary 1 (⟨(55 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(55 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(55 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(55 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(55 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ55]
  rw [kzero _ gm55_0]
  rw [kzero _ gm55_3]
  rw [kzero _ gm55_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb55_0_0_4 (add_le_add cb55_0_1_3 (add_le_add cb55_0_2_2 (add_le_add cb55_1_0_3 (add_le_add gb55_1 gb55_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp56 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25143229641837184147977535553400000000000000000000000000 := by
  decide +kernel

theorem cb56_0_0_4 :
    ((∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25143229641837184147977535553400000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25143229641837184147977535553400000000000000000000000000 cm56_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_0_1_3 :
    ∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84449556636185545252022464446600000000000000000000000000 := by
  decide +kernel

theorem cb56_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84449556636185545252022464446600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84449556636185545252022464446600000000000000000000000000 cm56_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm56_1_0_3 :
    ∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84449556636185545252022464446600000000000000000000000000 := by
  decide +kernel

theorem cb56_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84449556636185545252022464446600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (56 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84449556636185545252022464446600000000000000000000000000 cm56_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm56_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm56_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25143229641837184147977535553400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb56_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25143229641837184147977535553400000000000000000000000000 * 78002213862783105084853216 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((56 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-41 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((78002213862783105084853216 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25143229641837184147977535553400000000000000000000000000 gm56_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm56_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm56_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(56 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (56 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg56 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (56 : Fin 88)),
            if yzBoundary 1 (⟨(56 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(56 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(56 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((56 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((56 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117073905391394583189489112794523945756879717106851088251967400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp56 (fun b ↦
    if yzBoundary 1 (⟨(56 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(56 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(56 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(56 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(56 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ56]
  rw [kzero _ gm56_0]
  rw [kzero _ gm56_1]
  rw [kzero _ gm56_3]
  rw [kzero _ gm56_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb56_0_0_4 (add_le_add cb56_0_1_3 (add_le_add cb56_1_0_3 gb56_2))) (le_of_eq (by push_cast; ring)))

theorem hsp57 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ57 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm57_3_0_1 :
    ∑ w, mu3 5 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84528744979326232919180167141724000000000000000000000000 := by
  decide +kernel

theorem cb57_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84528744979326232919180167141724000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84528744979326232919180167141724000000000000000000000000 cm57_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm57_4_0_0 :
    ∑ w, mu3 5 2 (⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 26259755656737668102819832858276000000000000000000000000 := by
  decide +kernel

theorem cb57_4_0_0 :
    ((∑ w, mu3 5 2 (⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((26259755656737668102819832858276000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (57 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26259755656737668102819832858276000000000000000000000000 cm57_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84528744979326232919180167141724000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb57_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84528744979326232919180167141724000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((57 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84528744979326232919180167141724000000000000000000000000 gm57_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26259755656737668102819832858276000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb57_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26259755656737668102819832858276000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((57 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26259755656737668102819832858276000000000000000000000000 gm57_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm57_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm57_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm57_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(57 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (57 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg57 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (57 : Fin 88)),
            if yzBoundary 1 (⟨(57 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(57 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(57 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((57 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((57 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76792736854351400561730534048836305921380956713286000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp57 (fun b ↦
    if yzBoundary 1 (⟨(57 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(57 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(57 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(57 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(57 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [hJ57]
  rw [kzero _ gm57_2]
  rw [kzero _ gm57_3]
  rw [kzero _ gm57_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb57_3_0_1 (add_le_add cb57_4_0_0 (add_le_add gb57_0 gb57_1))) (le_of_eq (by push_cast; ring)))

theorem hsp58 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ58 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm58_0_3_1 :
    ∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 927093085251294474308963848834780000000000000000000000000 := by
  decide +kernel

theorem cb58_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((927093085251294474308963848834780000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 927093085251294474308963848834780000000000000000000000000 cm58_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm58_0_4_0 :
    ∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 24936747043642670461510594375900000000000000000000000000 := by
  decide +kernel

theorem cb58_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(58 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((24936747043642670461510594375900000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24936747043642670461510594375900000000000000000000000000 cm58_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm58_3_0_1 :
    ∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 24936747043642670461510594375900000000000000000000000000 := by
  decide +kernel

theorem cb58_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((24936747043642670461510594375900000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (58 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24936747043642670461510594375900000000000000000000000000 cm58_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37962440374579510517358489405624100000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb58_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37962440374579510517358489405624100000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((58 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37962440374579510517358489405624100000000000000000000000000 gm58_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37035347289328216043049525556789320000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb58_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37035347289328216043049525556789320000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((58 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37035347289328216043049525556789320000000000000000000000000 gm58_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm58_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm58_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm58_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(58 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (58 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg58 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (58 : Fin 88)),
            if yzBoundary 1 (⟨(58 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(58 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(58 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((58 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((58 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((26330843348720459291161837759988233912974803051441660000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp58 (fun b ↦
    if yzBoundary 1 (⟨(58 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(58 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(58 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(58 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(58 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ58]
  rw [kzero _ gm58_2]
  rw [kzero _ gm58_3]
  rw [kzero _ gm58_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb58_0_3_1 (add_le_add cb58_0_4_0 (add_le_add cb58_3_0_1 (add_le_add gb58_0 gb58_1)))) (le_of_eq (by push_cast; ring)))

theorem hsp59 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 5 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 812537517293621228189846011828340000000000000000000000000 := by
  decide +kernel

theorem cb59_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((812537517293621228189846011828340000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (59 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 812537517293621228189846011828340000000000000000000000000 cm59_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm59_0_4_0 :
    ∑ w, mu3 5 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 31309140321448071728090165839580000000000000000000000000 := by
  decide +kernel

theorem cb59_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((31309140321448071728090165839580000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (59 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat68.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 31309140321448071728090165839580000000000000000000000000 cm59_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2327095923012045268811909834160420000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb59_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2327095923012045268811909834160420000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((59 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.1 2327095923012045268811909834160420000000000000000000000000 gm59_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1545867546039872112350153988171660000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb59_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1545867546039872112350153988171660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((59 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.1 1545867546039872112350153988171660000000000000000000000000 gm59_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm59_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm59_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm59_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(59 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (59 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg59 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (59 : Fin 88)),
            if yzBoundary 1 (⟨(59 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(59 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(59 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((59 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((59 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1634721820267910161463522595638595219636861233427020000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp59 (fun b ↦
    if yzBoundary 1 (⟨(59 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(59 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(59 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(59 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(59 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(59 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ59]
  rw [kzero _ gm59_2]
  rw [kzero _ gm59_3]
  rw [kzero _ gm59_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb59_0_3_1 (add_le_add cb59_0_4_0 (add_le_add gb59_0 gb59_1))) (le_of_eq (by push_cast; ring)))

theorem hsp60 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
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

theorem cm60_0_3_1 :
    ∑ w, mu3 5 2 (⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84494647820656810220814759887640000000000000000000000000 := by
  decide +kernel

theorem cb60_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84494647820656810220814759887640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (60 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.1 84494647820656810220814759887640000000000000000000000000 cm60_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm60_0_4_0 :
    ∑ w, mu3 5 2 (⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25138194595738044609185240112360000000000000000000000000 := by
  decide +kernel

theorem cb60_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25138194595738044609185240112360000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (60 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.1 25138194595738044609185240112360000000000000000000000000 cm60_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84494647820656810220814759887640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb60_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84494647820656810220814759887640000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((60 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.1 84494647820656810220814759887640000000000000000000000000 gm60_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25138194595738044609185240112360000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb60_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25138194595738044609185240112360000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((60 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.1 25138194595738044609185240112360000000000000000000000000 gm60_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm60_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm60_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm60_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(60 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (60 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg60 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (60 : Fin 88)),
            if yzBoundary 1 (⟨(60 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(60 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(60 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((60 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((60 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((75991695617696875261062842795139393886698523112790000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp60 (fun b ↦
    if yzBoundary 1 (⟨(60 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(60 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(60 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(60 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(60 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(60 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(60 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ60]
  rw [kzero _ gm60_2]
  rw [kzero _ gm60_3]
  rw [kzero _ gm60_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb60_0_3_1 (add_le_add cb60_0_4_0 (add_le_add gb60_0 gb60_1))) (le_of_eq (by push_cast; ring)))

theorem hsp61 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ61 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm61_2_0_2 :
    ∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 332163831724254360267775109948808000000000000000000000000 := by
  decide +kernel

theorem cb61_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((332163831724254360267775109948808000000000000000000000000 * 319501305154271677087811261982 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((319501305154271677087811261982 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 332163831724254360267775109948808000000000000000000000000 cm61_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm61_3_0_1 :
    ∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 592608723968396260183911894121212000000000000000000000000 := by
  decide +kernel

theorem cb61_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((592608723968396260183911894121212000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 592608723968396260183911894121212000000000000000000000000 cm61_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm61_4_0_0 :
    ∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 13721739191064044214312995929980000000000000000000000000 := by
  decide +kernel

theorem cb61_4_0_0 :
    ((∑ w, mu3 5 2 (⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((13721739191064044214312995929980000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (61 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13721739191064044214312995929980000000000000000000000000 cm61_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 332163831724254360267775109948808000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb61_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((332163831724254360267775109948808000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((61 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 332163831724254360267775109948808000000000000000000000000 gm61_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 592608723968396260183911894121212000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb61_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((592608723968396260183911894121212000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((61 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 592608723968396260183911894121212000000000000000000000000 gm61_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13721739191064044214312995929980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb61_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13721739191064044214312995929980000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((61 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13721739191064044214312995929980000000000000000000000000 gm61_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm61_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm61_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(61 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (61 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg61 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (61 : Fin 88)),
            if yzBoundary 1 (⟨(61 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(61 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(61 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((61 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((61 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((927656910148784643995228697364761483116449734654838677130733376000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp61 (fun b ↦
    if yzBoundary 1 (⟨(61 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(61 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(61 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(61 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(61 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(61 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(61 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [hJ61]
  rw [kzero _ gm61_3]
  rw [kzero _ gm61_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb61_2_0_2 (add_le_add cb61_3_0_1 (add_le_add cb61_4_0_0 (add_le_add gb61_0 (add_le_add gb61_1 gb61_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp62 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ62 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm62_0_2_2 :
    ∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 19317571748509014825014769742440000000000000000000000000 := by
  decide +kernel

theorem cb62_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((19317571748509014825014769742440000000000000000000000000 * 125062099026323270542177968 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((125062099026323270542177968 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19317571748509014825014769742440000000000000000000000000 cm62_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_2_0_2 :
    ∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 8217704460640383341842943871434880000000000000000000000000 := by
  decide +kernel

theorem cb62_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((8217704460640383341842943871434880000000000000000000000000 * 342215644469666723789004189236 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((342215644469666723789004189236 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8217704460640383341842943871434880000000000000000000000000 cm62_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_3_0_1 :
    ∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2214536792178956881664407376412360000000000000000000000000 := by
  decide +kernel

theorem cb62_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2214536792178956881664407376412360000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2214536792178956881664407376412360000000000000000000000000 cm62_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm62_4_0_0 :
    ∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 19317571748509014825014769742440000000000000000000000000 := by
  decide +kernel

theorem cb62_4_0_0 :
    ((∑ w, mu3 5 2 (⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((19317571748509014825014769742440000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (62 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19317571748509014825014769742440000000000000000000000000 cm62_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10592565116638729149368125627511160000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb62_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10592565116638729149368125627511160000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((62 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10592565116638729149368125627511160000000000000000000000000 gm62_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 34025771606299246360589311829080440000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb62_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((34025771606299246360589311829080440000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((62 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 34025771606299246360589311829080440000000000000000000000000 gm62_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2374860655998345807525181756076280000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb62_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2374860655998345807525181756076280000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((62 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2374860655998345807525181756076280000000000000000000000000 gm62_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm62_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm62_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(62 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (62 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg62 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (62 : Fin 88)),
            if yzBoundary 1 (⟨(62 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(62 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(62 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((62 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((62 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27932097032983448297366939097574573903350227273085308251079779560000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp62 (fun b ↦
    if yzBoundary 1 (⟨(62 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(62 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(62 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(62 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(62 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [hJ62]
  rw [kzero _ gm62_3]
  rw [kzero _ gm62_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb62_0_2_2 (add_le_add cb62_2_0_2 (add_le_add cb62_3_0_1 (add_le_add cb62_4_0_0 (add_le_add gb62_0 (add_le_add gb62_1 gb62_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp63 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ63 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm63_0_2_2 :
    ∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 818896449939993638819052745942240000000000000000000000000 := by
  decide +kernel

theorem cb63_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((818896449939993638819052745942240000000000000000000000000 * 249740798198116262833109372162 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-40 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((249740798198116262833109372162 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 818896449939993638819052745942240000000000000000000000000 cm63_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_0_3_1 :
    ∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 113936387055573796830751015299660000000000000000000000000 := by
  decide +kernel

theorem cb63_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((113936387055573796830751015299660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 113936387055573796830751015299660000000000000000000000000 cm63_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_2_0_2 :
    ∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 861235926618656744613796143410100000000000000000000000000 := by
  decide +kernel

theorem cb63_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((861235926618656744613796143410100000000000000000000000000 * 426278380718519975826627576145 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((426278380718519975826627576145 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 861235926618656744613796143410100000000000000000000000000 cm63_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm63_3_0_1 :
    ∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 113936387055573796830751015299660000000000000000000000000 := by
  decide +kernel

theorem cb63_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((113936387055573796830751015299660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (63 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 113936387055573796830751015299660000000000000000000000000 cm63_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13982942344385282296521422068031890000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13982942344385282296521422068031890000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13982942344385282296521422068031890000000000000000000000000 gm63_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 47071065915606918015035653833336900000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((47071065915606918015035653833336900000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 47071065915606918015035653833336900000000000000000000000000 gm63_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12302809967826631913088573178679550000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb63_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12302809967826631913088573178679550000000000000000000000000 * 181441351400376553179138100488 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((63 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181441351400376553179138100488 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12302809967826631913088573178679550000000000000000000000000 gm63_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm63_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm63_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(63 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (63 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg63 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (63 : Fin 88)),
            if yzBoundary 1 (⟨(63 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(63 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(63 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((63 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((63 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((35589002572105511168699316785950222683541771429519624013198448330000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp63 (fun b ↦
    if yzBoundary 1 (⟨(63 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(63 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(63 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(63 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(63 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ63]
  rw [kzero _ gm63_3]
  rw [kzero _ gm63_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb63_0_2_2 (add_le_add cb63_0_3_1 (add_le_add cb63_2_0_2 (add_le_add cb63_3_0_1 (add_le_add gb63_0 (add_le_add gb63_1 gb63_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp64 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ64 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm64_0_2_2 :
    ∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 409762236340579319314523953087600000000000000000000000000 := by
  decide +kernel

theorem cb64_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((409762236340579319314523953087600000000000000000000000000 * 302955218006102328592512063211 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((302955218006102328592512063211 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 409762236340579319314523953087600000000000000000000000000 cm64_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm64_0_3_1 :
    ∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 95203520746721230030568724080960000000000000000000000000 := by
  decide +kernel

theorem cb64_0_3_1 :
    ((∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((95203520746721230030568724080960000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 95203520746721230030568724080960000000000000000000000000 cm64_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm64_0_4_0 :
    ∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 893625539451978811421301757160000000000000000000000000 := by
  decide +kernel

theorem cb64_0_4_0 :
    ((∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((893625539451978811421301757160000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 893625539451978811421301757160000000000000000000000000 cm64_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm64_2_0_2 :
    ∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 893625539451978811421301757160000000000000000000000000 := by
  decide +kernel

theorem cb64_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((893625539451978811421301757160000000000000000000000000 * 345885938136950246525113192650 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (64 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((345885938136950246525113192650 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 893625539451978811421301757160000000000000000000000000 cm64_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 515737810532728414222494768176440000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb64_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((515737810532728414222494768176440000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((64 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 515737810532728414222494768176440000000000000000000000000 gm64_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1675136268007511087981599136051840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb64_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1675136268007511087981599136051840000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((64 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1675136268007511087981599136051840000000000000000000000000 gm64_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 105975574192149094907970815088840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb64_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((105975574192149094907970815088840000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((64 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 105975574192149094907970815088840000000000000000000000000 gm64_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm64_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm64_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(64 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (64 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg64 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (64 : Fin 88)),
            if yzBoundary 1 (⟨(64 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(64 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(64 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((64 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((64 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1351554733357370024757874564806451367470308614071949750173111480000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp64 (fun b ↦
    if yzBoundary 1 (⟨(64 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(64 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(64 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(64 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(64 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ64]
  rw [kzero _ gm64_3]
  rw [kzero _ gm64_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb64_0_2_2 (add_le_add cb64_0_3_1 (add_le_add cb64_0_4_0 (add_le_add cb64_2_0_2 (add_le_add gb64_0 (add_le_add gb64_1 gb64_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp65 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ65 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm65_0_1_3 :
    ∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 109155286072273107523483592746350000000000000000000000000 := by
  decide +kernel

theorem cb65_0_1_3 :
    ((∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((109155286072273107523483592746350000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 109155286072273107523483592746350000000000000000000000000 cm65_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_0_2_2 :
    ∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 741544710178655622951852942421758000000000000000000000000 := by
  decide +kernel

theorem cb65_0_2_2 :
    ((∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((741544710178655622951852942421758000000000000000000000000 * 416226441690597092722607245975 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416226441690597092722607245975 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 741544710178655622951852942421758000000000000000000000000 cm65_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_1_0_3 :
    ∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 795051061376617434033823039459976000000000000000000000000 := by
  decide +kernel

theorem cb65_1_0_3 :
    ((∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((795051061376617434033823039459976000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 795051061376617434033823039459976000000000000000000000000 cm65_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_2_0_2 :
    ∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 10688688618890305487309623529053476000000000000000000000000 := by
  decide +kernel

theorem cb65_2_0_2 :
    ((∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((10688688618890305487309623529053476000000000000000000000000 * 434224377014837342720231636657 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((434224377014837342720231636657 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10688688618890305487309623529053476000000000000000000000000 cm65_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm65_3_0_1 :
    ∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 741544710178655622951852942421758000000000000000000000000 := by
  decide +kernel

theorem cb65_3_0_1 :
    ((∑ w, mu3 5 2 (⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 (⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((741544710178655622951852942421758000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (65 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 741544710178655622951852942421758000000000000000000000000 cm65_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 904206347448890541557306632206326000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 5 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb65_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((904206347448890541557306632206326000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((65 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 904206347448890541557306632206326000000000000000000000000 gm65_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 31449774040636611668572840425371916000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 5 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb65_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((31449774040636611668572840425371916000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((65 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31449774040636611668572840425371916000000000000000000000000 gm65_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20761085421746306181263216896318440000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 5 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb65_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20761085421746306181263216896318440000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((65 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat69.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 20761085421746306181263216896318440000000000000000000000000 gm65_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm65_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 5 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm65_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 5 2 ⟨(65 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (65 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg65 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (65 : Fin 88)),
            if yzBoundary 1 (⟨(65 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨(65 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(65 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr ((65 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr ((65 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27890009583728079931463136576661152920014810854870051669552467144000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp65 (fun b ↦
    if yzBoundary 1 (⟨(65 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 2 ⟨(65 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 2 ⟨(65 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(65 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(65 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ65]
  rw [kzero _ gm65_3]
  rw [kzero _ gm65_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb65_0_1_3 (add_le_add cb65_0_2_2 (add_le_add cb65_1_0_3 (add_le_add cb65_2_0_2 (add_le_add cb65_3_0_1 (add_le_add gb65_0 (add_le_add gb65_1 gb65_2))))))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 5 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((231610989586980023633521378766505932288035013695999499445095227413000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg44 (add_le_add L3K.reg45 (add_le_add L3K.reg46 (add_le_add L3K.reg47 (add_le_add L3K.reg48 (add_le_add L3K.reg49 (add_le_add L3K.reg50 (add_le_add L3K.reg51 (add_le_add L3K.reg52 (add_le_add L3K.reg53 (add_le_add L3K.reg54 (add_le_add L3K.reg55 (add_le_add L3K.reg56 (add_le_add L3K.reg57 (add_le_add L3K.reg58 (add_le_add L3K.reg59 (add_le_add L3K.reg60 (add_le_add L3K.reg61 (add_le_add L3K.reg62 (add_le_add L3K.reg63 (add_le_add L3K.reg64 L3K.reg65))))))))))))))))))))) (le_of_eq (by push_cast; ring))
