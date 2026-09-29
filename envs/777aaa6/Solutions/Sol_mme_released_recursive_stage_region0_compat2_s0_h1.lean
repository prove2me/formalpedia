-- Prove2me | solution 1 for mme_released_recursive_stage_region0_compat2_s0_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T12:45:10.052263+00:00
-- url     : https://prove2.me/submissions/db75f936-0fa5-4646-877a-b6a2aa9681a5

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat3
import Theorems.Thm_mme_released_recursive_level3_compat4
import Theorems.Thm_mme_released_recursive_level3_compat5
import Theorems.Thm_mme_released_recursive_level3_compat6
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

theorem hsp22 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ22 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm22_0_2_2 :
    ∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 293114730273284135470855120895232000000000000000000000000 := by
  decide +kernel

theorem cb22_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((293114730273284135470855120895232000000000000000000000000 * 302907740767913280417545613763 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((302907740767913280417545613763 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 293114730273284135470855120895232000000000000000000000000 cm22_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm22_0_3_1 :
    ∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 68187797079640179557148780139776000000000000000000000000 := by
  decide +kernel

theorem cb22_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(22 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((68187797079640179557148780139776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 68187797079640179557148780139776000000000000000000000000 cm22_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm22_0_4_0 :
    ∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 639552419524641906975700636992000000000000000000000000 := by
  decide +kernel

theorem cb22_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(22 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((639552419524641906975700636992000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 639552419524641906975700636992000000000000000000000000 cm22_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm22_2_0_2 :
    ∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 639552419524641906975700636992000000000000000000000000 := by
  decide +kernel

theorem cb22_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(22 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(22 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((639552419524641906975700636992000000000000000000000000 * 344668317573666961364914180434 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -8 else if k.val = 2 then 4 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((344668317573666961364914180434 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 639552419524641906975700636992000000000000000000000000 cm22_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 368864895681269590192786353470976000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (22 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((368864895681269590192786353470976000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 368864895681269590192786353470976000000000000000000000000 gm22_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1198388287129651765459327111644288000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (22 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1198388287129651765459327111644288000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1198388287129651765459327111644288000000000000000000000000 gm22_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 75750165407985454721931232575744000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (22 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((75750165407985454721931232575744000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 75750165407985454721931232575744000000000000000000000000 gm22_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (22 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm22_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (22 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg22 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (22 : Fin 88)),
            if yzBoundary 1 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((22 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((22 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((966930795923641079133364168872158573913562288410791162152782912000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp22 (fun b ↦
    if yzBoundary 1 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(22 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(22 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(22 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(22 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(22 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(22 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(22 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ22]
  rw [kzero _ gm22_3]
  rw [kzero _ gm22_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb22_0_2_2 (add_le_add cb22_0_3_1 (add_le_add cb22_0_4_0 (add_le_add cb22_2_0_2 (add_le_add gb22_0 (add_le_add gb22_1 gb22_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp23 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ23 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm23_0_3_1 :
    ∑ w, mu3 0 2 (⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 805640489340510564921175466836568000000000000000000000000 := by
  decide +kernel

theorem cb23_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((805640489340510564921175466836568000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (23 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 805640489340510564921175466836568000000000000000000000000 cm23_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm23_0_4_0 :
    ∑ w, mu3 0 2 (⟨(23 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 31027718570873723316234852234160000000000000000000000000 := by
  decide +kernel

theorem cb23_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(23 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(23 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((31027718570873723316234852234160000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (23 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31027718570873723316234852234160000000000000000000000000 cm23_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2307374712050154952531765147765840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (23 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2307374712050154952531765147765840000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2307374712050154952531765147765840000000000000000000000000 gm23_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1532761941280518110926824533163432000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (23 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1532761941280518110926824533163432000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1532761941280518110926824533163432000000000000000000000000 gm23_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (23 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (23 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (23 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg23 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (23 : Fin 88)),
            if yzBoundary 1 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((23 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((23 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1620857051799489147919276933801272086140161956786024000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp23 (fun b ↦
    if yzBoundary 1 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(23 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(23 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(23 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(23 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(23 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(23 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ23]
  rw [kzero _ gm23_2]
  rw [kzero _ gm23_3]
  rw [kzero _ gm23_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb23_0_3_1 (add_le_add cb23_0_4_0 (add_le_add gb23_0 gb23_1))) (le_of_eq (by push_cast; ring)))

theorem hsp24 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ24 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm24_0_0_4 :
    ∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3067371156408848851438560637744000000000000000000000000 := by
  decide +kernel

theorem cb24_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3067371156408848851438560637744000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3067371156408848851438560637744000000000000000000000000 cm24_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_0_1_3 :
    ∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 117048799046040588037397330168288000000000000000000000000 := by
  decide +kernel

theorem cb24_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((117048799046040588037397330168288000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 117048799046040588037397330168288000000000000000000000000 cm24_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_1_0_3 :
    ∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 608684224763142995221149771217968000000000000000000000000 := by
  decide +kernel

theorem cb24_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((608684224763142995221149771217968000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 608684224763142995221149771217968000000000000000000000000 cm24_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_2_0_2 :
    ∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3940077074733229400938014337976000000000000000000000000000 := by
  decide +kernel

theorem cb24_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(24 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3940077074733229400938014337976000000000000000000000000000 * 380597898598862061535576420098 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380597898598862061535576420098 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3940077074733229400938014337976000000000000000000000000000 cm24_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_3_0_1 :
    ∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 117048799046040588037397330168288000000000000000000000000 := by
  decide +kernel

theorem cb24_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(24 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(24 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((117048799046040588037397330168288000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 117048799046040588037397330168288000000000000000000000000 cm24_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3067371156408848851438560637744000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (24 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3067371156408848851438560637744000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.1 3067371156408848851438560637744000000000000000000000000 gm24_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 608684224763142995221149771217968000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (24 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((608684224763142995221149771217968000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 608684224763142995221149771217968000000000000000000000000 gm24_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3940077074733229400938014337976000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (24 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3940077074733229400938014337976000000000000000000000000000 * 10401396666853381688117865962 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10401396666853381688117865962 : ℚ)/10^30) mme_released_recursive_level3_compat3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3940077074733229400938014337976000000000000000000000000000 gm24_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (24 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm24_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (24 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg24 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (24 : Fin 88)),
            if yzBoundary 1 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((24 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((24 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2546646958098452857906481949224889407015724755950199069776123488000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp24 (fun b ↦
    if yzBoundary 1 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(24 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(24 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(24 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(24 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(24 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ24]
  rw [kzero _ gm24_3]
  rw [kzero _ gm24_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb24_0_0_4 (add_le_add cb24_0_1_3 (add_le_add cb24_1_0_3 (add_le_add cb24_2_0_2 (add_le_add cb24_3_0_1 (add_le_add gb24_0 (add_le_add gb24_1 gb24_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp25 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ25 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm25_0_1_3 :
    ∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 109730296220667996618117608744260000000000000000000000000 := by
  decide +kernel

theorem cb25_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((109730296220667996618117608744260000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.1 109730296220667996618117608744260000000000000000000000000 cm25_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_0_2_2 :
    ∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 745417423487880140249219281448336000000000000000000000000 := by
  decide +kernel

theorem cb25_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(25 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((745417423487880140249219281448336000000000000000000000000 * 416224128115806053698556484656 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416224128115806053698556484656 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.1 745417423487880140249219281448336000000000000000000000000 cm25_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_1_0_3 :
    ∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 799283737217513397198414443354492000000000000000000000000 := by
  decide +kernel

theorem cb25_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((799283737217513397198414443354492000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.1 799283737217513397198414443354492000000000000000000000000 cm25_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_2_0_2 :
    ∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 10745111137310373871633732584730240000000000000000000000000 := by
  decide +kernel

theorem cb25_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((10745111137310373871633732584730240000000000000000000000000 * 434222852724432781418104350015 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((434222852724432781418104350015 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.1 10745111137310373871633732584730240000000000000000000000000 cm25_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_3_0_1 :
    ∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 745417423487880140249219281448336000000000000000000000000 := by
  decide +kernel

theorem cb25_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((745417423487880140249219281448336000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.1 745417423487880140249219281448336000000000000000000000000 cm25_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 909014033438181393816532052098752000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (25 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((909014033438181393816532052098752000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.1 909014033438181393816532052098752000000000000000000000000 gm25_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 31615801108775310063458248666452912000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (25 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((31615801108775310063458248666452912000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.1 31615801108775310063458248666452912000000000000000000000000 gm25_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20870689971464936191824516081722672000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (25 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20870689971464936191824516081722672000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.1 20870689971464936191824516081722672000000000000000000000000 gm25_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (25 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm25_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (25 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg25 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (25 : Fin 88)),
            if yzBoundary 1 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((25 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((25 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((28037201427547139493032323887319104317382254643743886118692435984000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp25 (fun b ↦
    if yzBoundary 1 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(25 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(25 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ25]
  rw [kzero _ gm25_3]
  rw [kzero _ gm25_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb25_0_1_3 (add_le_add cb25_0_2_2 (add_le_add cb25_1_0_3 (add_le_add cb25_2_0_2 (add_le_add cb25_3_0_1 (add_le_add gb25_0 (add_le_add gb25_1 gb25_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp26 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ26 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm26_0_2_2 :
    ∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 823488648514449639626516390847420000000000000000000000000 := by
  decide +kernel

theorem cb26_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((823488648514449639626516390847420000000000000000000000000 * 249728112387343464838619542817 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((249728112387343464838619542817 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 823488648514449639626516390847420000000000000000000000000 cm26_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm26_0_3_1 :
    ∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 114572200638372347414639087127630000000000000000000000000 := by
  decide +kernel

theorem cb26_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((114572200638372347414639087127630000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 114572200638372347414639087127630000000000000000000000000 cm26_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm26_2_0_2 :
    ∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 866167730637250342166136702238830000000000000000000000000 := by
  decide +kernel

theorem cb26_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((866167730637250342166136702238830000000000000000000000000 * 426276133601652018576984295813 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then -1 else if k.val = 2 then 5 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((426276133601652018576984295813 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 866167730637250342166136702238830000000000000000000000000 cm26_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm26_3_0_1 :
    ∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 114572200638372347414639087127630000000000000000000000000 := by
  decide +kernel

theorem cb26_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(26 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(26 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((114572200638372347414639087127630000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 114572200638372347414639087127630000000000000000000000000 cm26_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14063100479842630975526013843277230000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (26 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14063100479842630975526013843277230000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14063100479842630975526013843277230000000000000000000000000 gm26_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 47340661911843847917098694139190280000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (26 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((47340661911843847917098694139190280000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 47340661911843847917098694139190280000000000000000000000000 gm26_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12373444100690930993733360750190980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (26 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12373444100690930993733360750190980000000000000000000000000 * 181445989627686224932960119827 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 7 else if k.val = 2 then 6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181445989627686224932960119827 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12373444100690930993733360750190980000000000000000000000000 gm26_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (26 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm26_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (26 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg26 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (26 : Fin 88)),
            if yzBoundary 1 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((26 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((26 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((35792863832707429983044785199579534298553327355613653867237175240000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp26 (fun b ↦
    if yzBoundary 1 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(26 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(26 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(26 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ26]
  rw [kzero _ gm26_3]
  rw [kzero _ gm26_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb26_0_2_2 (add_le_add cb26_0_3_1 (add_le_add cb26_2_0_2 (add_le_add cb26_3_0_1 (add_le_add gb26_0 (add_le_add gb26_1 gb26_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp27 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ27 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm27_0_3_1 :
    ∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 927154161128007061899274106214870000000000000000000000000 := by
  decide +kernel

theorem cb27_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((927154161128007061899274106214870000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 927154161128007061899274106214870000000000000000000000000 cm27_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm27_0_4_0 :
    ∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 24935740290909304244030052923830000000000000000000000000 := by
  decide +kernel

theorem cb27_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((24935740290909304244030052923830000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24935740290909304244030052923830000000000000000000000000 cm27_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm27_3_0_1 :
    ∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 24935740290909304244030052923830000000000000000000000000 := by
  decide +kernel

theorem cb27_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(27 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(27 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((24935740290909304244030052923830000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24935740290909304244030052923830000000000000000000000000 cm27_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37967871655311729157985969947076170000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (27 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37967871655311729157985969947076170000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37967871655311729157985969947076170000000000000000000000000 gm27_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37040717494183722096086695840861300000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (27 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37040717494183722096086695840861300000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37040717494183722096086695840861300000000000000000000000000 gm27_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (27 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (27 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (27 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg27 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (27 : Fin 88)),
            if yzBoundary 1 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((27 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((27 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((26334607327819007543414318654932044328724443890008990000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp27 (fun b ↦
    if yzBoundary 1 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(27 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(27 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(27 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(27 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ27]
  rw [kzero _ gm27_2]
  rw [kzero _ gm27_3]
  rw [kzero _ gm27_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb27_0_3_1 (add_le_add cb27_0_4_0 (add_le_add cb27_3_0_1 (add_le_add gb27_0 gb27_1)))) (le_of_eq (by push_cast; ring)))

theorem hsp28 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ28 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm28_0_2_2 :
    ∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 18818676108155136508264692960533000000000000000000000000 := by
  decide +kernel

theorem cb28_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((18818676108155136508264692960533000000000000000000000000 * 126625612999872158882996087 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((126625612999872158882996087 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18818676108155136508264692960533000000000000000000000000 cm28_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_2_0_2 :
    ∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 8006676334516506212034183474781495000000000000000000000000 := by
  decide +kernel

theorem cb28_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(28 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((8006676334516506212034183474781495000000000000000000000000 * 342213798339249040248270784098 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((342213798339249040248270784098 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8006676334516506212034183474781495000000000000000000000000 cm28_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_3_0_1 :
    ∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2157608980174153521110780028700012000000000000000000000000 := by
  decide +kernel

theorem cb28_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(28 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2157608980174153521110780028700012000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2157608980174153521110780028700012000000000000000000000000 cm28_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_4_0_0 :
    ∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 18818676108155136508264692960533000000000000000000000000 := by
  decide +kernel

theorem cb28_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((18818676108155136508264692960533000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18818676108155136508264692960533000000000000000000000000 cm28_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10320336871552522712903741401666925000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (28 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10320336871552522712903741401666925000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10320336871552522712903741401666925000000000000000000000000 gm28_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33151728097593206792031207782045072000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (28 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33151728097593206792031207782045072000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33151728097593206792031207782045072000000000000000000000000 gm28_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2313660537036016500869557926885430000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (28 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2313660537036016500869557926885430000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2313660537036016500869557926885430000000000000000000000000 gm28_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (28 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm28_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (28 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg28 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (28 : Fin 88)),
            if yzBoundary 1 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((28 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((28 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27214564946329451560192845552942159377835055166666963101542161601000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp28 (fun b ↦
    if yzBoundary 1 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(28 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(28 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(28 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(28 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(28 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(28 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ28]
  rw [kzero _ gm28_3]
  rw [kzero _ gm28_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb28_0_2_2 (add_le_add cb28_2_0_2 (add_le_add cb28_3_0_1 (add_le_add cb28_4_0_0 (add_le_add gb28_0 (add_le_add gb28_1 gb28_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp29 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ29 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm29_2_0_2 :
    ∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 337353399499313295228128254481842000000000000000000000000 := by
  decide +kernel

theorem cb29_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(29 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((337353399499313295228128254481842000000000000000000000000 * 319503724212226995180563354554 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((319503724212226995180563354554 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 337353399499313295228128254481842000000000000000000000000 cm29_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_3_0_1 :
    ∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 601877756116856983562644439322894000000000000000000000000 := by
  decide +kernel

theorem cb29_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((601877756116856983562644439322894000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 601877756116856983562644439322894000000000000000000000000 cm29_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_4_0_0 :
    ∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 13942881052232537783227306195264000000000000000000000000 := by
  decide +kernel

theorem cb29_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((13942881052232537783227306195264000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13942881052232537783227306195264000000000000000000000000 cm29_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 337353399499313295228128254481842000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (29 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((337353399499313295228128254481842000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 337353399499313295228128254481842000000000000000000000000 gm29_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 601877756116856983562644439322894000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (29 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((601877756116856983562644439322894000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 601877756116856983562644439322894000000000000000000000000 gm29_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13942881052232537783227306195264000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (29 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13942881052232537783227306195264000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13942881052232537783227306195264000000000000000000000000 gm29_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (29 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm29_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (29 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg29 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (29 : Fin 88)),
            if yzBoundary 1 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((29 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((29 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((942165406903977421557699297654037701704320858363403854544989786000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp29 (fun b ↦
    if yzBoundary 1 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(29 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(29 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(29 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ29]
  rw [kzero _ gm29_3]
  rw [kzero _ gm29_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb29_2_0_2 (add_le_add cb29_3_0_1 (add_le_add cb29_4_0_0 (add_le_add gb29_0 (add_le_add gb29_1 gb29_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp30 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ30 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm30_3_0_1 :
    ∑ w, mu3 0 2 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84545700133826233074981978097020000000000000000000000000 := by
  decide +kernel

theorem cb30_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84545700133826233074981978097020000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84545700133826233074981978097020000000000000000000000000 cm30_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm30_4_0_0 :
    ∑ w, mu3 0 2 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 26263042345240796795018021902980000000000000000000000000 := by
  decide +kernel

theorem cb30_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((26263042345240796795018021902980000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26263042345240796795018021902980000000000000000000000000 cm30_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84545700133826233074981978097020000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (30 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84545700133826233074981978097020000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84545700133826233074981978097020000000000000000000000000 gm30_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26263042345240796795018021902980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (30 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26263042345240796795018021902980000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26263042345240796795018021902980000000000000000000000000 gm30_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (30 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (30 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (30 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg30 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (30 : Fin 88)),
            if yzBoundary 1 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((30 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((30 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76806767430758356378941944724478467555977581388310000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp30 (fun b ↦
    if yzBoundary 1 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(30 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ30]
  rw [kzero _ gm30_2]
  rw [kzero _ gm30_3]
  rw [kzero _ gm30_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb30_3_0_1 (add_le_add cb30_4_0_0 (add_le_add gb30_0 gb30_1))) (le_of_eq (by push_cast; ring)))

theorem hsp31 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ31 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm31_0_0_4 :
    ∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25139852137708930269337114425520000000000000000000000000 := by
  decide +kernel

theorem cb31_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(31 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25139852137708930269337114425520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25139852137708930269337114425520000000000000000000000000 cm31_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm31_0_1_3 :
    ∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84494050887349816170662885574480000000000000000000000000 := by
  decide +kernel

theorem cb31_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(31 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84494050887349816170662885574480000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84494050887349816170662885574480000000000000000000000000 cm31_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm31_1_0_3 :
    ∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84494050887349816170662885574480000000000000000000000000 := by
  decide +kernel

theorem cb31_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(31 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(31 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84494050887349816170662885574480000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84494050887349816170662885574480000000000000000000000000 cm31_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (31 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm31_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (31 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm31_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25139852137708930269337114425520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (31 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25139852137708930269337114425520000000000000000000000000 * 21411442903648427896397600 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((21411442903648427896397600 : ℚ)/10^30) mme_released_recursive_level3_compat4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25139852137708930269337114425520000000000000000000000000 gm31_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (31 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm31_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (31 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg31 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (31 : Fin 88)),
            if yzBoundary 1 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((31 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((31 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117134164573818793159126934937076501313923409307986343614624400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp31 (fun b ↦
    if yzBoundary 1 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(31 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(31 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(31 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(31 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ31]
  rw [kzero _ gm31_0]
  rw [kzero _ gm31_1]
  rw [kzero _ gm31_3]
  rw [kzero _ gm31_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb31_0_0_4 (add_le_add cb31_0_1_3 (add_le_add cb31_1_0_3 gb31_2))) (le_of_eq (by push_cast; ring)))

theorem hsp32 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ32 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm32_0_0_4 :
    ∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 50803717098116850306704763840144000000000000000000000000 := by
  decide +kernel

theorem cb32_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(32 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((50803717098116850306704763840144000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.1 50803717098116850306704763840144000000000000000000000000 cm32_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm32_0_1_3 :
    ∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2469929532319243572601945357007396000000000000000000000000 := by
  decide +kernel

theorem cb32_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(32 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2469929532319243572601945357007396000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.1 2469929532319243572601945357007396000000000000000000000000 cm32_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm32_0_2_2 :
    ∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1331957148570240797669349879152460000000000000000000000000 := by
  decide +kernel

theorem cb32_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1331957148570240797669349879152460000000000000000000000000 * 380293914508853252419266648920 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 6 else if k.val = 2 then 8 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 7 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380293914508853252419266648920 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.1 1331957148570240797669349879152460000000000000000000000000 cm32_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm32_1_0_3 :
    ∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1331957148570240797669349879152460000000000000000000000000 := by
  decide +kernel

theorem cb32_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(32 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(32 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1331957148570240797669349879152460000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.1 1331957148570240797669349879152460000000000000000000000000 cm32_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (32 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm32_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 50803717098116850306704763840144000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (32 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((50803717098116850306704763840144000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.1 50803717098116850306704763840144000000000000000000000000 gm32_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2469929532319243572601945357007396000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (32 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2469929532319243572601945357007396000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.1 2469929532319243572601945357007396000000000000000000000000 gm32_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (32 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm32_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (32 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg32 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (32 : Fin 88)),
            if yzBoundary 1 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((32 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((32 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3177016684923306481999387120411169615138540149111007424820275980000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp32 (fun b ↦
    if yzBoundary 1 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(32 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(32 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(32 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ32]
  rw [kzero _ gm32_0]
  rw [kzero _ gm32_3]
  rw [kzero _ gm32_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb32_0_0_4 (add_le_add cb32_0_1_3 (add_le_add cb32_0_2_2 (add_le_add cb32_1_0_3 (add_le_add gb32_1 gb32_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp33 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ33 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm33_0_0_4 :
    ∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 4690958773424314979225934281106000000000000000000000000 := by
  decide +kernel

theorem cb33_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(33 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((4690958773424314979225934281106000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.1 4690958773424314979225934281106000000000000000000000000 cm33_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_0_1_3 :
    ∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 877360065228467261719595617321494000000000000000000000000 := by
  decide +kernel

theorem cb33_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(33 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((877360065228467261719595617321494000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.1 877360065228467261719595617321494000000000000000000000000 cm33_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_0_2_2 :
    ∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 6091392783138726862750290623446536000000000000000000000000 := by
  decide +kernel

theorem cb33_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((6091392783138726862750290623446536000000000000000000000000 * 371054325897876427558133729696 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((371054325897876427558133729696 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6091392783138726862750290623446536000000000000000000000000 cm33_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_0_3_1 :
    ∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 175136596473294527088887824950864000000000000000000000000 := by
  decide +kernel

theorem cb33_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(33 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((175136596473294527088887824950864000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 175136596473294527088887824950864000000000000000000000000 cm33_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_1_0_3 :
    ∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 175136596473294527088887824950864000000000000000000000000 := by
  decide +kernel

theorem cb33_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(33 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(33 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((175136596473294527088887824950864000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 175136596473294527088887824950864000000000000000000000000 cm33_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4690958773424314979225934281106000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (33 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4690958773424314979225934281106000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4690958773424314979225934281106000000000000000000000000 gm33_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 877360065228467261719595617321494000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (33 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((877360065228467261719595617321494000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 877360065228467261719595617321494000000000000000000000000 gm33_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6091392783138726862750290623446536000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (33 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6091392783138726862750290623446536000000000000000000000000 * 5013375506769988527471632250 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5013375506769988527471632250 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6091392783138726862750290623446536000000000000000000000000 gm33_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (33 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm33_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (33 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg33 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (33 : Fin 88)),
            if yzBoundary 1 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((33 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((33 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3749846269522494341691358608461458964018301404803707163475122836000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp33 (fun b ↦
    if yzBoundary 1 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(33 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(33 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(33 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(33 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(33 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ33]
  rw [kzero _ gm33_3]
  rw [kzero _ gm33_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb33_0_0_4 (add_le_add cb33_0_1_3 (add_le_add cb33_0_2_2 (add_le_add cb33_0_3_1 (add_le_add cb33_1_0_3 (add_le_add gb33_0 (add_le_add gb33_1 gb33_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp34 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ34 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm34_0_2_2 :
    ∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 359657421378014735818784632111200000000000000000000000000 := by
  decide +kernel

theorem cb34_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(34 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((359657421378014735818784632111200000000000000000000000000 * 319447043940856206786695085817 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (34 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -4 else if k.val = 2 then -3 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((319447043940856206786695085817 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 359657421378014735818784632111200000000000000000000000000 cm34_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm34_0_3_1 :
    ∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 641177714880818313114944246656800000000000000000000000000 := by
  decide +kernel

theorem cb34_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(34 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((641177714880818313114944246656800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (34 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 641177714880818313114944246656800000000000000000000000000 cm34_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm34_0_4_0 :
    ∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 14891086404620724666271121232000000000000000000000000000 := by
  decide +kernel

theorem cb34_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(34 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(34 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((14891086404620724666271121232000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (34 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14891086404620724666271121232000000000000000000000000000 cm34_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 359657421378014735818784632111200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (34 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((359657421378014735818784632111200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 359657421378014735818784632111200000000000000000000000000 gm34_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 641177714880818313114944246656800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (34 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((641177714880818313114944246656800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 641177714880818313114944246656800000000000000000000000000 gm34_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14891086404620724666271121232000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (34 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14891086404620724666271121232000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14891086404620724666271121232000000000000000000000000000 gm34_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (34 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm34_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (34 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg34 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (34 : Fin 88)),
            if yzBoundary 1 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((34 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((34 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1003752550705613117344849557622958189954582626713113145768758400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp34 (fun b ↦
    if yzBoundary 1 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(34 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(34 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(34 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(34 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(34 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ34]
  rw [kzero _ gm34_3]
  rw [kzero _ gm34_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb34_0_2_2 (add_le_add cb34_0_3_1 (add_le_add cb34_0_4_0 (add_le_add gb34_0 (add_le_add gb34_1 gb34_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp35 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ35 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm35_0_3_1 :
    ∑ w, mu3 0 2 (⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84557919782881566296714053421695000000000000000000000000 := by
  decide +kernel

theorem cb35_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84557919782881566296714053421695000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84557919782881566296714053421695000000000000000000000000 cm35_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm35_0_4_0 :
    ∑ w, mu3 0 2 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 26297888449387912018285946578305000000000000000000000000 := by
  decide +kernel

theorem cb35_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((26297888449387912018285946578305000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26297888449387912018285946578305000000000000000000000000 cm35_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84557919782881566296714053421695000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (35 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84557919782881566296714053421695000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84557919782881566296714053421695000000000000000000000000 gm35_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26297888449387912018285946578305000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (35 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26297888449387912018285946578305000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26297888449387912018285946578305000000000000000000000000 gm35_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (35 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm35_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (35 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm35_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (35 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg35 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (35 : Fin 88)),
            if yzBoundary 1 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((35 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((35 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76839390924891563735428979943977091087821898218095000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp35 (fun b ↦
    if yzBoundary 1 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ35]
  rw [kzero _ gm35_2]
  rw [kzero _ gm35_3]
  rw [kzero _ gm35_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb35_0_3_1 (add_le_add cb35_0_4_0 (add_le_add gb35_0 gb35_1))) (le_of_eq (by push_cast; ring)))

theorem hsp36 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ36 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm36_0_0_4 :
    ∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 45723045534459690546981409352632000000000000000000000000 := by
  decide +kernel

theorem cb36_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((45723045534459690546981409352632000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45723045534459690546981409352632000000000000000000000000 cm36_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm36_0_1_3 :
    ∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1193509405403196965348955228976008000000000000000000000000 := by
  decide +kernel

theorem cb36_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1193509405403196965348955228976008000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1193509405403196965348955228976008000000000000000000000000 cm36_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm36_1_0_3 :
    ∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2220621307131960614752063361671360000000000000000000000000 := by
  decide +kernel

theorem cb36_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2220621307131960614752063361671360000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2220621307131960614752063361671360000000000000000000000000 cm36_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm36_2_0_2 :
    ∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1193509405403196965348955228976008000000000000000000000000 := by
  decide +kernel

theorem cb36_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1193509405403196965348955228976008000000000000000000000000 * 380497984256130257033552131414 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((380497984256130257033552131414 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1193509405403196965348955228976008000000000000000000000000 cm36_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (36 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm36_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 45723045534459690546981409352632000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (36 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((45723045534459690546981409352632000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45723045534459690546981409352632000000000000000000000000 gm36_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2220621307131960614752063361671360000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (36 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2220621307131960614752063361671360000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2220621307131960614752063361671360000000000000000000000000 gm36_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (36 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm36_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (36 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg36 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (36 : Fin 88)),
            if yzBoundary 1 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((36 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((36 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2852315800502335361177704354744025638017464555845242794466283256000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp36 (fun b ↦
    if yzBoundary 1 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ36]
  rw [kzero _ gm36_0]
  rw [kzero _ gm36_3]
  rw [kzero _ gm36_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb36_0_0_4 (add_le_add cb36_0_1_3 (add_le_add cb36_1_0_3 (add_le_add cb36_2_0_2 (add_le_add gb36_1 gb36_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp37 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ37 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm37_0_0_4 :
    ∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 22600263300352215296355845561344000000000000000000000000 := by
  decide +kernel

theorem cb37_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((22600263300352215296355845561344000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22600263300352215296355845561344000000000000000000000000 cm37_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm37_0_1_3 :
    ∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2560024353968488988572563210486848000000000000000000000000 := by
  decide +kernel

theorem cb37_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2560024353968488988572563210486848000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2560024353968488988572563210486848000000000000000000000000 cm37_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm37_0_2_2 :
    ∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 10347596715862924747250719733746256000000000000000000000000 := by
  decide +kernel

theorem cb37_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((10347596715862924747250719733746256000000000000000000000000 * 408084171396412987778783465295 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((408084171396412987778783465295 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10347596715862924747250719733746256000000000000000000000000 cm37_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm37_1_0_3 :
    ∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2586569976556095554954176201058104000000000000000000000000 := by
  decide +kernel

theorem cb37_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2586569976556095554954176201058104000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2586569976556095554954176201058104000000000000000000000000 cm37_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm37_2_0_2 :
    ∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 10347596715862924747250719733746256000000000000000000000000 := by
  decide +kernel

theorem cb37_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((10347596715862924747250719733746256000000000000000000000000 * 407862992158721033091205570859 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 1 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -7 else if k.val = 2 then 5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((407862992158721033091205570859 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10347596715862924747250719733746256000000000000000000000000 cm37_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22600263300352215296355845561344000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (37 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22600263300352215296355845561344000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22600263300352215296355845561344000000000000000000000000 gm37_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5146594330524584543526739411544952000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (37 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5146594330524584543526739411544952000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5146594330524584543526739411544952000000000000000000000000 gm37_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 39489093727799571203644370018294896000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (37 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((39489093727799571203644370018294896000000000000000000000000 * 22924607186556977162369956601 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -1 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((22924607186556977162369956601 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 39489093727799571203644370018294896000000000000000000000000 gm37_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (37 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm37_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (37 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg37 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (37 : Fin 88)),
            if yzBoundary 1 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((37 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((37 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((16483058851161539720707075733312304124696089366362808374994346160000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp37 (fun b ↦
    if yzBoundary 1 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ37]
  rw [kzero _ gm37_3]
  rw [kzero _ gm37_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb37_0_0_4 (add_le_add cb37_0_1_3 (add_le_add cb37_0_2_2 (add_le_add cb37_1_0_3 (add_le_add cb37_2_0_2 (add_le_add gb37_0 (add_le_add gb37_1 gb37_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp38 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ38 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm38_0_2_2 :
    ∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2313639548908895676096693547264944000000000000000000000000 := by
  decide +kernel

theorem cb38_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2313639548908895676096693547264944000000000000000000000000 * 323239673510684550773677761563 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((323239673510684550773677761563 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2313639548908895676096693547264944000000000000000000000000 cm38_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_0_3_1 :
    ∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 601027969876983067457103729363504000000000000000000000000 := by
  decide +kernel

theorem cb38_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((601027969876983067457103729363504000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 601027969876983067457103729363504000000000000000000000000 cm38_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_0_4_0 :
    ∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5429060705671850023401402623664000000000000000000000000 := by
  decide +kernel

theorem cb38_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5429060705671850023401402623664000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5429060705671850023401402623664000000000000000000000000 cm38_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_2_0_2 :
    ∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5429060705671850023401402623664000000000000000000000000 := by
  decide +kernel

theorem cb38_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5429060705671850023401402623664000000000000000000000000 * 347152286557941902964414707703 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((347152286557941902964414707703 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5429060705671850023401402623664000000000000000000000000 cm38_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2993086241732899488632414535648288000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (38 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2993086241732899488632414535648288000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2993086241732899488632414535648288000000000000000000000000 gm38_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9572332544737487082719264394092592000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (38 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9572332544737487082719264394092592000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9572332544737487082719264394092592000000000000000000000000 gm38_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 679446692824003812535720988383344000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (38 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((679446692824003812535720988383344000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 679446692824003812535720988383344000000000000000000000000 gm38_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (38 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm38_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (38 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg38 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (38 : Fin 88)),
            if yzBoundary 1 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((38 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((38 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((7801380960773449048140054115015061518655481076865817418286754912000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp38 (fun b ↦
    if yzBoundary 1 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(38 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(38 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ38]
  rw [kzero _ gm38_3]
  rw [kzero _ gm38_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb38_0_2_2 (add_le_add cb38_0_3_1 (add_le_add cb38_0_4_0 (add_le_add cb38_2_0_2 (add_le_add gb38_0 (add_le_add gb38_1 gb38_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp39 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ39 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm39_0_3_1 :
    ∑ w, mu3 0 2 (⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 626246608433285286741558136164864000000000000000000000000 := by
  decide +kernel

theorem cb39_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((626246608433285286741558136164864000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (39 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 626246608433285286741558136164864000000000000000000000000 cm39_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm39_0_4_0 :
    ∑ w, mu3 0 2 (⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25807815192464471942134118329856000000000000000000000000 := by
  decide +kernel

theorem cb39_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25807815192464471942134118329856000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (39 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.1 25807815192464471942134118329856000000000000000000000000 cm39_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1752640709397877850489865881670144000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (39 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1752640709397877850489865881670144000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.1 1752640709397877850489865881670144000000000000000000000000 gm39_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1152201916157057035690441863835136000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (39 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1152201916157057035690441863835136000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.1 1152201916157057035690441863835136000000000000000000000000 gm39_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (39 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm39_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (39 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm39_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (39 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg39 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (39 : Fin 88)),
            if yzBoundary 1 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((39 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((39 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1232726580590790345412752285193486000522945106191616000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp39 (fun b ↦
    if yzBoundary 1 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(39 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ39]
  rw [kzero _ gm39_2]
  rw [kzero _ gm39_3]
  rw [kzero _ gm39_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb39_0_3_1 (add_le_add cb39_0_4_0 (add_le_add gb39_0 gb39_1))) (le_of_eq (by push_cast; ring)))

theorem hsp40 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ40 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm40_0_0_4 :
    ∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 510643628362398483692677567980000000000000000000000000 := by
  decide +kernel

theorem cb40_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(40 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((510643628362398483692677567980000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.1 510643628362398483692677567980000000000000000000000000 cm40_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm40_0_1_3 :
    ∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19026493270432389746166006340952000000000000000000000000 := by
  decide +kernel

theorem cb40_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19026493270432389746166006340952000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.1 19026493270432389746166006340952000000000000000000000000 cm40_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm40_1_0_3 :
    ∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 97194891067843354930035778262614000000000000000000000000 := by
  decide +kernel

theorem cb40_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((97194891067843354930035778262614000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.1 97194891067843354930035778262614000000000000000000000000 cm40_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm40_2_0_2 :
    ∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 672809247331677718222105537828454000000000000000000000000 := by
  decide +kernel

theorem cb40_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((672809247331677718222105537828454000000000000000000000000 * 370617639512139048826148608496 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370617639512139048826148608496 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.1 672809247331677718222105537828454000000000000000000000000 cm40_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm40_3_0_1 :
    ∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19026493270432389746166006340952000000000000000000000000 := by
  decide +kernel

theorem cb40_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19026493270432389746166006340952000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.1 19026493270432389746166006340952000000000000000000000000 cm40_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 510643628362398483692677567980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (40 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((510643628362398483692677567980000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.1 510643628362398483692677567980000000000000000000000000 gm40_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 97194891067843354930035778262614000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (40 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((97194891067843354930035778262614000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.1 97194891067843354930035778262614000000000000000000000000 gm40_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 672809247331677718222105537828454000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (40 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((672809247331677718222105537828454000000000000000000000000 * 5069950604219255950431920921 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -1 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5069950604219255950431920921 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.1 672809247331677718222105537828454000000000000000000000000 gm40_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (40 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm40_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (40 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg40 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (40 : Fin 88)),
            if yzBoundary 1 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((40 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((40 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((413883134487738111070891519171153010708310210590957752503825830000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp40 (fun b ↦
    if yzBoundary 1 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(40 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(40 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ40]
  rw [kzero _ gm40_3]
  rw [kzero _ gm40_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb40_0_0_4 (add_le_add cb40_0_1_3 (add_le_add cb40_1_0_3 (add_le_add cb40_2_0_2 (add_le_add cb40_3_0_1 (add_le_add gb40_0 (add_le_add gb40_1 gb40_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp41 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ41 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm41_0_1_3 :
    ∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 105944216532719893300690920639192000000000000000000000000 := by
  decide +kernel

theorem cb41_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((105944216532719893300690920639192000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 105944216532719893300690920639192000000000000000000000000 cm41_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm41_0_2_2 :
    ∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 723958304801420219249995963387092000000000000000000000000 := by
  decide +kernel

theorem cb41_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((723958304801420219249995963387092000000000000000000000000 * 416567857728319826301626138517 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416567857728319826301626138517 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 723958304801420219249995963387092000000000000000000000000 cm41_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm41_1_0_3 :
    ∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 778402705408764198861219339513414000000000000000000000000 := by
  decide +kernel

theorem cb41_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((778402705408764198861219339513414000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 778402705408764198861219339513414000000000000000000000000 cm41_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm41_2_0_2 :
    ∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 10522889938081471204810173913651398000000000000000000000000 := by
  decide +kernel

theorem cb41_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((10522889938081471204810173913651398000000000000000000000000 * 433328745657473716315500910045 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (1 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((433328745657473716315500910045 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10522889938081471204810173913651398000000000000000000000000 cm41_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm41_3_0_1 :
    ∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 723958304801420219249995963387092000000000000000000000000 := by
  decide +kernel

theorem cb41_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(41 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(41 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((723958304801420219249995963387092000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 723958304801420219249995963387092000000000000000000000000 cm41_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 884346921941484092161910260152606000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (41 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((884346921941484092161910260152606000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 884346921941484092161910260152606000000000000000000000000 gm41_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 30967129399896995935462093776460302000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (41 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((30967129399896995935462093776460302000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 30967129399896995935462093776460302000000000000000000000000 gm41_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20444239461815524730651919862808904000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (41 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20444239461815524730651919862808904000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 20444239461815524730651919862808904000000000000000000000000 gm41_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (41 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm41_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (41 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg41 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (41 : Fin 88)),
            if yzBoundary 1 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((41 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((41 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27441019124646510350012219619770971040822805336517922000829046044000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp41 (fun b ↦
    if yzBoundary 1 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(41 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(41 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(41 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(41 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(41 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(41 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ41]
  rw [kzero _ gm41_3]
  rw [kzero _ gm41_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb41_0_1_3 (add_le_add cb41_0_2_2 (add_le_add cb41_1_0_3 (add_le_add cb41_2_0_2 (add_le_add cb41_3_0_1 (add_le_add gb41_0 (add_le_add gb41_1 gb41_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp42 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ42 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm42_0_2_2 :
    ∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 652690910757500379065165379935340000000000000000000000000 := by
  decide +kernel

theorem cb42_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((652690910757500379065165379935340000000000000000000000000 * 253824896586340502257158648749 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((253824896586340502257158648749 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 652690910757500379065165379935340000000000000000000000000 cm42_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_0_3_1 :
    ∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 92316930979527999319521016857660000000000000000000000000 := by
  decide +kernel

theorem cb42_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((92316930979527999319521016857660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92316930979527999319521016857660000000000000000000000000 cm42_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_2_0_2 :
    ∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 703987028636412710912920679096688000000000000000000000000 := by
  decide +kernel

theorem cb42_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((703987028636412710912920679096688000000000000000000000000 * 425450656670354577358645711880 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((425450656670354577358645711880 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 703987028636412710912920679096688000000000000000000000000 cm42_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_3_0_1 :
    ∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 92316930979527999319521016857660000000000000000000000000 := by
  decide +kernel

theorem cb42_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((92316930979527999319521016857660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92316930979527999319521016857660000000000000000000000000 cm42_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11241358411734018213265605764198844000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (42 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11241358411734018213265605764198844000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11241358411734018213265605764198844000000000000000000000000 gm42_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37829189886726590547461746437886992000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (42 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37829189886726590547461746437886992000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37829189886726590547461746437886992000000000000000000000000 gm42_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9884680472340105123287519705166816000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (42 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9884680472340105123287519705166816000000000000000000000000 * 180783559862715826094034074983 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((180783559862715826094034074983 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9884680472340105123287519705166816000000000000000000000000 gm42_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (42 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm42_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (42 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg42 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (42 : Fin 88)),
            if yzBoundary 1 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((42 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((42 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((28601343424145902884749541255527507865051195129796329776644513008000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp42 (fun b ↦
    if yzBoundary 1 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ42]
  rw [kzero _ gm42_3]
  rw [kzero _ gm42_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb42_0_2_2 (add_le_add cb42_0_3_1 (add_le_add cb42_2_0_2 (add_le_add cb42_3_0_1 (add_le_add gb42_0 (add_le_add gb42_1 gb42_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp43 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ43 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm43_0_3_1 :
    ∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 746799202381763154123967955326878000000000000000000000000 := by
  decide +kernel

theorem cb43_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((746799202381763154123967955326878000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 746799202381763154123967955326878000000000000000000000000 cm43_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm43_0_4_0 :
    ∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19575973175054149504477457367230000000000000000000000000 := by
  decide +kernel

theorem cb43_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19575973175054149504477457367230000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19575973175054149504477457367230000000000000000000000000 cm43_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm43_3_0_1 :
    ∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 19575973175054149504477457367230000000000000000000000000 := by
  decide +kernel

theorem cb43_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((19575973175054149504477457367230000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19575973175054149504477457367230000000000000000000000000 cm43_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29965668535306782315789522542632770000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (43 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29965668535306782315789522542632770000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29965668535306782315789522542632770000000000000000000000000 gm43_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29218869332925019161665554587305892000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (43 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29218869332925019161665554587305892000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29218869332925019161665554587305892000000000000000000000000 gm43_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (43 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm43_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (43 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm43_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (43 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg43 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (43 : Fin 88)),
            if yzBoundary 1 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((43 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((43 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((20784187689454768041392952533763726858380275376048822000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp43 (fun b ↦
    if yzBoundary 1 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(43 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(43 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ43]
  rw [kzero _ gm43_2]
  rw [kzero _ gm43_3]
  rw [kzero _ gm43_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb43_0_3_1 (add_le_add cb43_0_4_0 (add_le_add cb43_3_0_1 (add_le_add gb43_0 gb43_1)))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((237267149140972505603173380206924554977192564143305646369349219837000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg22 (add_le_add L3K.reg23 (add_le_add L3K.reg24 (add_le_add L3K.reg25 (add_le_add L3K.reg26 (add_le_add L3K.reg27 (add_le_add L3K.reg28 (add_le_add L3K.reg29 (add_le_add L3K.reg30 (add_le_add L3K.reg31 (add_le_add L3K.reg32 (add_le_add L3K.reg33 (add_le_add L3K.reg34 (add_le_add L3K.reg35 (add_le_add L3K.reg36 (add_le_add L3K.reg37 (add_le_add L3K.reg38 (add_le_add L3K.reg39 (add_le_add L3K.reg40 (add_le_add L3K.reg41 (add_le_add L3K.reg42 L3K.reg43))))))))))))))))))))) (le_of_eq (by push_cast; ring))
