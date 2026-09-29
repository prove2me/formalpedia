-- Prove2me | solution 1 for mme_released_recursive_stage_region1_compat1_s0_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T13:17:55.958315+00:00
-- url     : https://prove2.me/submissions/65acb9a4-f30c-4bba-9099-376c7a68c673

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat15
import Theorems.Thm_mme_released_recursive_level3_compat16
import Theorems.Thm_mme_released_recursive_level3_compat17
import Theorems.Thm_mme_released_recursive_level3_compat18
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



noncomputable abbrev MU := partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)

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

theorem kstepC (a : Fin 88) (b : Split (2 * 2 ^ (2 - 1)) (parent3 1 a))
    (hb : yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 1 1 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 1 1 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp22 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
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

theorem cm22_2_2_0 :
    ∑ w, mu3 1 1 (⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 22309398323173519096065370650300000000000000000000000000 := by
  decide +kernel

theorem cb22_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((22309398323173519096065370650300000000000000000000000000 * 279468833231815538305885609416 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((279468833231815538305885609416 : ℚ)/10^30) mme_released_recursive_level3_compat15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22309398323173519096065370650300000000000000000000000000 cm22_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12821205661254068760824353286868156000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12821205661254068760824353286868156000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12821205661254068760824353286868156000000000000000000000000 gm22_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 44133770917945614110167293426263688000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((44133770917945614110167293426263688000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 44133770917945614110167293426263688000000000000000000000000 gm22_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12798896262930895241728287916217856000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12798896262930895241728287916217856000000000000000000000000 * 371559365770661185761381445394 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((371559365770661185761381445394 : ℚ)/10^30) mme_released_recursive_level3_compat15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12798896262930895241728287916217856000000000000000000000000 gm22_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm22_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg22 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (22 : Fin 88)),
            if yzBoundary 0 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((22 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((22 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((35352983438791081996974174038553553262551348469843480079664639284000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp22 (fun b ↦
    if yzBoundary 0 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(22 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ22]
  rw [kzero _ gm22_3]
  rw [kzero _ gm22_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb22_2_2_0 (add_le_add gb22_0 (add_le_add gb22_1 gb22_2))) (le_of_eq (by push_cast; ring)))

theorem hsp23 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
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

theorem gm23_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3447291078618988929820000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3447291078618988929820000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.1 3447291078618988929820000000000000000000000000000000000000 gm23_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3447291078618988929820000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3447291078618988929820000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.1 3447291078618988929820000000000000000000000000000000000000 gm23_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg23 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (23 : Fin 88)),
            if yzBoundary 0 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((23 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((23 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2389480091714204940824527555825890606557634916087660000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp23 (fun b ↦
    if yzBoundary 0 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ23]
  rw [kzero _ gm23_2]
  rw [kzero _ gm23_3]
  rw [kzero _ gm23_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb23_0 gb23_1) (le_of_eq (by push_cast; ring)))

theorem hsp24 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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

theorem cm24_0_4_0 :
    ∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 21199832017212776418390561001606000000000000000000000000 := by
  decide +kernel

theorem cb24_0_4_0 :
    ((∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(24 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((21199832017212776418390561001606000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21199832017212776418390561001606000000000000000000000000 cm24_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_1_3_0 :
    ∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 4034967099017650727185153687720086000000000000000000000000 := by
  decide +kernel

theorem cb24_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((4034967099017650727185153687720086000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4034967099017650727185153687720086000000000000000000000000 cm24_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_2_2_0 :
    ∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 27434863795116455626440467705601354000000000000000000000000 := by
  decide +kernel

theorem cb24_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(24 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((27434863795116455626440467705601354000000000000000000000000 * 378218868360593638048764752058 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378218868360593638048764752058 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 27434863795116455626440467705601354000000000000000000000000 cm24_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm24_3_1_0 :
    ∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 800937260862345402761988045676954000000000000000000000000 := by
  decide +kernel

theorem cb24_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(24 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(24 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((800937260862345402761988045676954000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (24 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 800937260862345402761988045676954000000000000000000000000 cm24_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21199832017212776418390561001606000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21199832017212776418390561001606000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21199832017212776418390561001606000000000000000000000000 gm24_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4034967099017650727185153687720086000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4034967099017650727185153687720086000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4034967099017650727185153687720086000000000000000000000000 gm24_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 27434863795116455626440467705601354000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((27434863795116455626440467705601354000000000000000000000000 * 18365524675874833857727280112 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 8 else if k.val = 2 then 7 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((18365524675874833857727280112 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 27434863795116455626440467705601354000000000000000000000000 gm24_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 800937260862345402761988045676954000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((800937260862345402761988045676954000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.1 800937260862345402761988045676954000000000000000000000000 gm24_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg24 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (24 : Fin 88)),
            if yzBoundary 0 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((24 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((24 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17584225751241176316471818195802922644817206340986400228658345144000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp24 (fun b ↦
    if yzBoundary 0 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(24 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(24 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(24 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(24 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ24]
  rw [kzero _ gm24_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb24_0_4_0 (add_le_add cb24_1_3_0 (add_le_add cb24_2_2_0 (add_le_add cb24_3_1_0 (add_le_add gb24_0 (add_le_add gb24_1 (add_le_add gb24_2 gb24_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp25 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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

theorem cm25_1_3_0 :
    ∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 819770592042224709784568134351668000000000000000000000000 := by
  decide +kernel

theorem cb25_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((819770592042224709784568134351668000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 819770592042224709784568134351668000000000000000000000000 cm25_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_2_2_0 :
    ∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 11633539637925316042350001857134106000000000000000000000000 := by
  decide +kernel

theorem cb25_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((11633539637925316042350001857134106000000000000000000000000 * 404227867206771529866179096767 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((404227867206771529866179096767 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11633539637925316042350001857134106000000000000000000000000 cm25_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm25_3_1_0 :
    ∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 774430082262735071400835369955970000000000000000000000000 := by
  decide +kernel

theorem cb25_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((774430082262735071400835369955970000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (25 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 774430082262735071400835369955970000000000000000000000000 cm25_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 928181542129194364460274297542640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((928181542129194364460274297542640000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 928181542129194364460274297542640000000000000000000000000 gm25_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33886365386047251478436890332501390000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33886365386047251478436890332501390000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33886365386047251478436890332501390000000000000000000000000 gm25_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 23027255830384670507487723845323254000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((23027255830384670507487723845323254000000000000000000000000 * 96363675732695487231686421811 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((96363675732695487231686421811 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 23027255830384670507487723845323254000000000000000000000000 gm25_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 108410950086969654675706163190972000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((108410950086969654675706163190972000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 108410950086969654675706163190972000000000000000000000000 gm25_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg25 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (25 : Fin 88)),
            if yzBoundary 0 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((25 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((25 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31589991003555627098019335316848684666560073747084820776243926776000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp25 (fun b ↦
    if yzBoundary 0 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(25 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(25 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(25 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ25]
  rw [kzero _ gm25_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb25_1_3_0 (add_le_add cb25_2_2_0 (add_le_add cb25_3_1_0 (add_le_add gb25_0 (add_le_add gb25_1 (add_le_add gb25_2 gb25_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp26 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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

theorem cm26_2_2_0 :
    ∑ w, mu3 1 1 (⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 867073598675387148132473062514588000000000000000000000000 := by
  decide +kernel

theorem cb26_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((867073598675387148132473062514588000000000000000000000000 * 399737825604143047895117551372 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 0 else if k.val = 2 then -2 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((399737825604143047895117551372 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 867073598675387148132473062514588000000000000000000000000 cm26_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm26_3_1_0 :
    ∑ w, mu3 1 1 (⟨(26 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 119118664541635032175952199498128000000000000000000000000 := by
  decide +kernel

theorem cb26_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(26 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(26 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((119118664541635032175952199498128000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (26 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 119118664541635032175952199498128000000000000000000000000 cm26_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13409598535891966345497413264160020000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13409598535891966345497413264160020000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13409598535891966345497413264160020000000000000000000000000 gm26_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 45696219731499288321305221272181832000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((45696219731499288321305221272181832000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 45696219731499288321305221272181832000000000000000000000000 gm26_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12542524937216579197364940201645432000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12542524937216579197364940201645432000000000000000000000000 * 207967983314757639304024888683 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 7 else if k.val = 2 then -3 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207967983314757639304024888683 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12542524937216579197364940201645432000000000000000000000000 gm26_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm26_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg26 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (26 : Fin 88)),
            if yzBoundary 0 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((26 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((26 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((34711818367456820797554451786435831103500965436810149613184060692000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp26 (fun b ↦
    if yzBoundary 0 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(26 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(26 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ26]
  rw [kzero _ gm26_3]
  rw [kzero _ gm26_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb26_2_2_0 (add_le_add cb26_3_1_0 (add_le_add gb26_0 (add_le_add gb26_1 gb26_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp27 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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

theorem cm27_3_1_0 :
    ∑ w, mu3 1 1 (⟨(27 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 844166098707229612687545360325000000000000000000000000 := by
  decide +kernel

theorem cb27_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(27 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(27 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((844166098707229612687545360325000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 844166098707229612687545360325000000000000000000000000 cm27_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1298656623467343632725000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1298656623467343632725000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1298656623467343632725000000000000000000000000000000000000 gm27_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1297812457368636403112312454639675000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1297812457368636403112312454639675000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1297812457368636403112312454639675000000000000000000000000 gm27_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg27 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (27 : Fin 88)),
            if yzBoundary 0 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((27 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((27 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((900160177071887745968450246331415359042825392225425000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp27 (fun b ↦
    if yzBoundary 0 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(27 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ27]
  rw [kzero _ gm27_2]
  rw [kzero _ gm27_3]
  rw [kzero _ gm27_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb27_3_1_0 (add_le_add gb27_0 gb27_1)) (le_of_eq (by push_cast; ring)))

theorem hsp28 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm28_2_2_0 :
    ∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 8036002095016839684094112076143910000000000000000000000000 := by
  decide +kernel

theorem cb28_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((8036002095016839684094112076143910000000000000000000000000 * 340037195816883602814110155454 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 8 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((340037195816883602814110155454 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8036002095016839684094112076143910000000000000000000000000 cm28_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_3_1_0 :
    ∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 2325187482269379056098267641132395000000000000000000000000 := by
  decide +kernel

theorem cb28_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(28 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((2325187482269379056098267641132395000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2325187482269379056098267641132395000000000000000000000000 cm28_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_4_0_0 :
    ∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 18883953362006632076680437749570000000000000000000000000 := by
  decide +kernel

theorem cb28_4_0_0 :
    ((∑ w, mu3 1 1 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((18883953362006632076680437749570000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18883953362006632076680437749570000000000000000000000000 cm28_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10198436284989858867001840750612060000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10198436284989858867001840750612060000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10198436284989858867001840750612060000000000000000000000000 gm28_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33432899724169778025014689982144345000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33432899724169778025014689982144345000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33432899724169778025014689982144345000000000000000000000000 gm28_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2181318143335025814984409112217720000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2181318143335025814984409112217720000000000000000000000000 * 4381806403699766240951319 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((4381806403699766240951319 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2181318143335025814984409112217720000000000000000000000000 gm28_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm28_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg28 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (28 : Fin 88)),
            if yzBoundary 0 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((28 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((28 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27518166505441889736772281341635840129704212150110026708102749670000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp28 (fun b ↦
    if yzBoundary 0 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ28]
  rw [kzero _ gm28_3]
  rw [kzero _ gm28_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb28_2_2_0 (add_le_add cb28_3_1_0 (add_le_add cb28_4_0_0 (add_le_add gb28_0 (add_le_add gb28_1 gb28_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp29 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm29_3_1_0 :
    ∑ w, mu3 1 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 323046547954524761843940291422325000000000000000000000000 := by
  decide +kernel

theorem cb29_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((323046547954524761843940291422325000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 323046547954524761843940291422325000000000000000000000000 cm29_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_4_0_0 :
    ∑ w, mu3 1 1 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 13354011222860881013366453277915000000000000000000000000 := by
  decide +kernel

theorem cb29_4_0_0 :
    ((∑ w, mu3 1 1 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((13354011222860881013366453277915000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.1 13354011222860881013366453277915000000000000000000000000 cm29_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 899200185936170482641633546722085000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((899200185936170482641633546722085000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 899200185936170482641633546722085000000000000000000000000 gm29_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 589507649204506601811059708577675000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((589507649204506601811059708577675000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat16.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 589507649204506601811059708577675000000000000000000000000 gm29_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm29_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm29_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg29 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (29 : Fin 88)),
            if yzBoundary 0 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((29 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((29 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((632534368868927043537226207317607681909934022727515000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp29 (fun b ↦
    if yzBoundary 0 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ29]
  rw [kzero _ gm29_2]
  rw [kzero _ gm29_3]
  rw [kzero _ gm29_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb29_3_1_0 (add_le_add cb29_4_0_0 (add_le_add gb29_0 gb29_1))) (le_of_eq (by push_cast; ring)))

theorem hsp30 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm30_3_1_0 :
    ∑ w, mu3 1 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 84540738109684072908774813353865000000000000000000000000 := by
  decide +kernel

theorem cb30_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((84540738109684072908774813353865000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.1 84540738109684072908774813353865000000000000000000000000 cm30_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm30_4_0_0 :
    ∑ w, mu3 1 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 26267744653027697336225186646135000000000000000000000000 := by
  decide +kernel

theorem cb30_4_0_0 :
    ((∑ w, mu3 1 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((26267744653027697336225186646135000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.1 26267744653027697336225186646135000000000000000000000000 cm30_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84540738109684072908774813353865000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84540738109684072908774813353865000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.1 84540738109684072908774813353865000000000000000000000000 gm30_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26267744653027697336225186646135000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26267744653027697336225186646135000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.1 26267744653027697336225186646135000000000000000000000000 gm30_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg30 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (30 : Fin 88)),
            if yzBoundary 0 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((30 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((30 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76806587409098962864750430657748561015547338013185000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp30 (fun b ↦
    if yzBoundary 0 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(30 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ30]
  rw [kzero _ gm30_2]
  rw [kzero _ gm30_3]
  rw [kzero _ gm30_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb30_3_1_0 (add_le_add cb30_4_0_0 (add_le_add gb30_0 gb30_1))) (le_of_eq (by push_cast; ring)))

theorem hsp31 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
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

theorem cm31_0_4_0 :
    ∑ w, mu3 1 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 25069823118650543072202973788600000000000000000000000000 := by
  decide +kernel

theorem cb31_0_4_0 :
    ((∑ w, mu3 1 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((25069823118650543072202973788600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25069823118650543072202973788600000000000000000000000000 cm31_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm31_1_3_0 :
    ∑ w, mu3 1 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 84626612211408136727797026211400000000000000000000000000 := by
  decide +kernel

theorem cb31_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((84626612211408136727797026211400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84626612211408136727797026211400000000000000000000000000 cm31_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm31_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm31_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25069823118650543072202973788600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25069823118650543072202973788600000000000000000000000000 * 21755948829873951734891355 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((21755948829873951734891355 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25069823118650543072202973788600000000000000000000000000 gm31_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84626612211408136727797026211400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84626612211408136727797026211400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84626612211408136727797026211400000000000000000000000000 gm31_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg31 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (31 : Fin 88)),
            if yzBoundary 0 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((31 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((31 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117317940727143720075378128011145097825606781388962231268610000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp31 (fun b ↦
    if yzBoundary 0 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ31]
  rw [kzero _ gm31_0]
  rw [kzero _ gm31_1]
  rw [kzero _ gm31_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb31_0_4_0 (add_le_add cb31_1_3_0 (add_le_add gb31_2 gb31_3))) (le_of_eq (by push_cast; ring)))

theorem hsp32 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ32 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm32_1_3_0 :
    ∑ w, mu3 1 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 6917627466477057220557355247104000000000000000000000000 := by
  decide +kernel

theorem cb32_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((6917627466477057220557355247104000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6917627466477057220557355247104000000000000000000000000 cm32_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 274481055856100985937069084225152000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((274481055856100985937069084225152000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 274481055856100985937069084225152000000000000000000000000 gm32_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10248942654950899320206930915774848000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10248942654950899320206930915774848000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10248942654950899320206930915774848000000000000000000000000 gm32_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10248942654950899320206930915774848000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10248942654950899320206930915774848000000000000000000000000 * 361193681075372835423506267215 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361193681075372835423506267215 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10248942654950899320206930915774848000000000000000000000000 gm32_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 267563428389623928716511728978048000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((267563428389623928716511728978048000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 267563428389623928716511728978048000000000000000000000000 gm32_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg32 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (32 : Fin 88)),
            if yzBoundary 0 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((32 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((32 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((10996134799655669600061828918346930343199917109703690919453584384000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp32 (fun b ↦
    if yzBoundary 0 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ32]
  rw [kzero _ gm32_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb32_1_3_0 (add_le_add gb32_0 (add_le_add gb32_1 (add_le_add gb32_2 gb32_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp33 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ33 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm33_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1195568755832225672116256255680000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1195568755832225672116256255680000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1195568755832225672116256255680000000000000000000000000000 gm33_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4083122002331542199767487488640000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4083122002331542199767487488640000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4083122002331542199767487488640000000000000000000000000000 gm33_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1195568755832225672116256255680000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1195568755832225672116256255680000000000000000000000000000 * 424527476488931482904145734802 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424527476488931482904145734802 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1195568755832225672116256255680000000000000000000000000000 gm33_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm33_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg33 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (33 : Fin 88)),
            if yzBoundary 0 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((33 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((33 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3337756290680853162552510447630636519528595882432274624896960000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp33 (fun b ↦
    if yzBoundary 0 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ33]
  rw [kzero _ gm33_3]
  rw [kzero _ gm33_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb33_0 (add_le_add gb33_1 gb33_2)) (le_of_eq (by push_cast; ring)))

theorem hsp34 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ34 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm34_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111371972178627657280000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111371972178627657280000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111371972178627657280000000000000000000000000000000000000 gm34_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111371972178627657280000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111371972178627657280000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111371972178627657280000000000000000000000000000000000000 gm34_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm34_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm34_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg34 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (34 : Fin 88)),
            if yzBoundary 0 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((34 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((34 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((77197168509016430335607599221048888488228399544640000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp34 (fun b ↦
    if yzBoundary 0 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ34]
  rw [kzero _ gm34_2]
  rw [kzero _ gm34_3]
  rw [kzero _ gm34_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb34_0 gb34_1) (le_of_eq (by push_cast; ring)))

theorem hsp35 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ35 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm35_0_4_0 :
    ∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 30998472331256852166899274035344000000000000000000000000 := by
  decide +kernel

theorem cb35_0_4_0 :
    ((∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((30998472331256852166899274035344000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 30998472331256852166899274035344000000000000000000000000 cm35_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm35_1_3_0 :
    ∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 1501040385160974421838765034028256000000000000000000000000 := by
  decide +kernel

theorem cb35_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((1501040385160974421838765034028256000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1501040385160974421838765034028256000000000000000000000000 cm35_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm35_2_2_0 :
    ∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 805509414108035390362335691936400000000000000000000000000 := by
  decide +kernel

theorem cb35_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((805509414108035390362335691936400000000000000000000000000 * 378224792993314335419740753915 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378224792993314335419740753915 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 805509414108035390362335691936400000000000000000000000000 cm35_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm35_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 30998472331256852166899274035344000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((30998472331256852166899274035344000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 30998472331256852166899274035344000000000000000000000000 gm35_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1501040385160974421838765034028256000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1501040385160974421838765034028256000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1501040385160974421838765034028256000000000000000000000000 gm35_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 805509414108035390362335691936400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((805509414108035390362335691936400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 805509414108035390362335691936400000000000000000000000000 gm35_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg35 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (35 : Fin 88)),
            if yzBoundary 0 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((35 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((35 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1924928625287675715271116344545669238639859099551945372387451200000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp35 (fun b ↦
    if yzBoundary 0 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(35 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(35 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ35]
  rw [kzero _ gm35_0]
  rw [kzero _ gm35_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb35_0_4_0 (add_le_add cb35_1_3_0 (add_le_add cb35_2_2_0 (add_le_add gb35_1 (add_le_add gb35_2 gb35_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp36 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ36 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm36_0_4_0 :
    ∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 493953374685310900473242905524000000000000000000000000 := by
  decide +kernel

theorem cb36_0_4_0 :
    ((∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(36 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((493953374685310900473242905524000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 493953374685310900473242905524000000000000000000000000 cm36_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm36_1_3_0 :
    ∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 58458253663867536405093840843303000000000000000000000000 := by
  decide +kernel

theorem cb36_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((58458253663867536405093840843303000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 58458253663867536405093840843303000000000000000000000000 cm36_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm36_2_2_0 :
    ∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 226392517040619643485364069998318000000000000000000000000 := by
  decide +kernel

theorem cb36_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(36 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(36 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((226392517040619643485364069998318000000000000000000000000 * 370426165432926434482294726742 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370426165432926434482294726742 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 226392517040619643485364069998318000000000000000000000000 cm36_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 493953374685310900473242905524000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((493953374685310900473242905524000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 493953374685310900473242905524000000000000000000000000 gm36_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111161381155252614229104862083234000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111161381155252614229104862083234000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111161381155252614229104862083234000000000000000000000000 gm36_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1099311109989571081689479720024166000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1099311109989571081689479720024166000000000000000000000000 * 188336776398103186884510347137 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((188336776398103186884510347137 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1099311109989571081689479720024166000000000000000000000000 gm36_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 52703127491385077824011021239931000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((52703127491385077824011021239931000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 52703127491385077824011021239931000000000000000000000000 gm36_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg36 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (36 : Fin 88)),
            if yzBoundary 0 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((36 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((36 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((445004818553947227781957843452649094595272630811724205688208842000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp36 (fun b ↦
    if yzBoundary 0 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(36 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ36]
  rw [kzero _ gm36_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb36_0_4_0 (add_le_add cb36_1_3_0 (add_le_add cb36_2_2_0 (add_le_add gb36_0 (add_le_add gb36_1 (add_le_add gb36_2 gb36_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp37 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ37 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm37_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2831677960029220116958000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2831677960029220116958000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2831677960029220116958000000000000000000000000000000000000 gm37_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2831677960029220116958000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2831677960029220116958000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat17.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2831677960029220116958000000000000000000000000000000000000 gm37_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm37_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm37_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg37 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (37 : Fin 88)),
            if yzBoundary 0 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((37 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((37 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1962769594247991433167228676192746860561117075520454000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp37 (fun b ↦
    if yzBoundary 0 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ37]
  rw [kzero _ gm37_2]
  rw [kzero _ gm37_3]
  rw [kzero _ gm37_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb37_0 gb37_1) (le_of_eq (by push_cast; ring)))

theorem hsp38 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ38 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm38_0_4_0 :
    ∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 25373176025561244980435292574000000000000000000000000000 := by
  decide +kernel

theorem cb38_0_4_0 :
    ((∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((25373176025561244980435292574000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.1 25373176025561244980435292574000000000000000000000000000 cm38_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_1_3_0 :
    ∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 4556439592298004752875236202717250000000000000000000000000 := by
  decide +kernel

theorem cb38_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((4556439592298004752875236202717250000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.1 4556439592298004752875236202717250000000000000000000000000 cm38_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_2_2_0 :
    ∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 33423332848937294371527480752050250000000000000000000000000 := by
  decide +kernel

theorem cb38_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((33423332848937294371527480752050250000000000000000000000000 * 368629817285449136871532532931 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 1 else if k.val = 2 then 8 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((368629817285449136871532532931 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.1 33423332848937294371527480752050250000000000000000000000000 cm38_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm38_3_1_0 :
    ∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 943508819081900719866847752658500000000000000000000000000 := by
  decide +kernel

theorem cb38_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((943508819081900719866847752658500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.1 943508819081900719866847752658500000000000000000000000000 cm38_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25373176025561244980435292574000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25373176025561244980435292574000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.1 25373176025561244980435292574000000000000000000000000000 gm38_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4556439592298004752875236202717250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4556439592298004752875236202717250000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.1 4556439592298004752875236202717250000000000000000000000000 gm38_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33423332848937294371527480752050250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33423332848937294371527480752050250000000000000000000000000 * 10584928988716915245489261377 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10584928988716915245489261377 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.1 33423332848937294371527480752050250000000000000000000000000 gm38_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 943508819081900719866847752658500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((943508819081900719866847752658500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.1 943508819081900719866847752658500000000000000000000000000 gm38_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg38 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (38 : Fin 88)),
            if yzBoundary 0 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((38 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((38 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((20299168155093019074985697266299802105398788575171565205840522000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp38 (fun b ↦
    if yzBoundary 0 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(38 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(38 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(38 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ38]
  rw [kzero _ gm38_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb38_0_4_0 (add_le_add cb38_1_3_0 (add_le_add cb38_2_2_0 (add_le_add cb38_3_1_0 (add_le_add gb38_0 (add_le_add gb38_1 (add_le_add gb38_2 gb38_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp39 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ39 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm39_1_3_0 :
    ∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 814616839343286001511385641572500000000000000000000000000 := by
  decide +kernel

theorem cb39_1_3_0 :
    ((∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((814616839343286001511385641572500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (39 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 814616839343286001511385641572500000000000000000000000000 cm39_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm39_2_2_0 :
    ∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 11628125709505274763098700850035000000000000000000000000000 := by
  decide +kernel

theorem cb39_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((11628125709505274763098700850035000000000000000000000000000 * 403510027416429865001133870000 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (39 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403510027416429865001133870000 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11628125709505274763098700850035000000000000000000000000000 cm39_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm39_3_1_0 :
    ∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 767223290765061380763505785915000000000000000000000000000 := by
  decide +kernel

theorem cb39_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(39 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(39 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((767223290765061380763505785915000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (39 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 767223290765061380763505785915000000000000000000000000000 cm39_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 921422564245252228271894386818750000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((921422564245252228271894386818750000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 921422564245252228271894386818750000000000000000000000000 gm39_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33873396720239431417214599827266250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33873396720239431417214599827266250000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33873396720239431417214599827266250000000000000000000000000 gm39_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 23012494301499218034879404763146250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((23012494301499218034879404763146250000000000000000000000000 * 95712587195618883182865826806 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -4 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((95712587195618883182865826806 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 23012494301499218034879404763146250000000000000000000000000 gm39_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 106805724901966226760508745246250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((106805724901966226760508745246250000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106805724901966226760508745246250000000000000000000000000 gm39_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg39 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (39 : Fin 88)),
            if yzBoundary 0 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((39 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((39 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31544380237252190460803821486429081962315664394115856050306108750000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp39 (fun b ↦
    if yzBoundary 0 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(39 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(39 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ39]
  rw [kzero _ gm39_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb39_1_3_0 (add_le_add cb39_2_2_0 (add_le_add cb39_3_1_0 (add_le_add gb39_0 (add_le_add gb39_1 (add_le_add gb39_2 gb39_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp40 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ40 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm40_2_2_0 :
    ∑ w, mu3 1 1 (⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 625327260520955973264669656452700000000000000000000000000 := by
  decide +kernel

theorem cb40_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((625327260520955973264669656452700000000000000000000000000 * 398986992587447676055890444966 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398986992587447676055890444966 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 625327260520955973264669656452700000000000000000000000000 cm40_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm40_3_1_0 :
    ∑ w, mu3 1 1 (⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 85070464451631054812161613495160000000000000000000000000 := by
  decide +kernel

theorem cb40_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((85070464451631054812161613495160000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (40 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85070464451631054812161613495160000000000000000000000000 cm40_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9524256099188583378989189373715840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9524256099188583378989189373715840000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9524256099188583378989189373715840000000000000000000000000 gm40_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32428461324806587786129459639073160000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32428461324806587786129459639073160000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32428461324806587786129459639073160000000000000000000000000 gm40_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8898928838667627405724519717263140000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8898928838667627405724519717263140000000000000000000000000 * 207637694076851887198876557263 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207637694076851887198876557263 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8898928838667627405724519717263140000000000000000000000000 gm40_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm40_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg40 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (40 : Fin 88)),
            if yzBoundary 0 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((40 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((40 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((24633913396643635584385478611605611467461574212592267099672714820000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp40 (fun b ↦
    if yzBoundary 0 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(40 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(40 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ40]
  rw [kzero _ gm40_3]
  rw [kzero _ gm40_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb40_2_2_0 (add_le_add cb40_3_1_0 (add_le_add gb40_0 (add_le_add gb40_1 gb40_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp41 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ41 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm41_3_1_0 :
    ∑ w, mu3 1 1 (⟨(41 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 3869707555091133789718279440690000000000000000000000000 := by
  decide +kernel

theorem cb41_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(41 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(41 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((3869707555091133789718279440690000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (41 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3869707555091133789718279440690000000000000000000000000 cm41_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5887082376587153617382000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5887082376587153617382000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5887082376587153617382000000000000000000000000000000000000 gm41_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5883212669032062483592281720559310000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5883212669032062483592281720559310000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5883212669032062483592281720559310000000000000000000000000 gm41_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm41_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm41_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg41 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (41 : Fin 88)),
            if yzBoundary 0 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((41 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((41 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4080614551055527717037965421782551697174777003025966000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp41 (fun b ↦
    if yzBoundary 0 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(41 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ41]
  rw [kzero _ gm41_2]
  rw [kzero _ gm41_3]
  rw [kzero _ gm41_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb41_3_1_0 (add_le_add gb41_0 gb41_1)) (le_of_eq (by push_cast; ring)))

theorem hsp42 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ42 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm42_2_2_0 :
    ∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 5357506648225348657910639018801216000000000000000000000000 := by
  decide +kernel

theorem cb42_2_2_0 :
    ((∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((5357506648225348657910639018801216000000000000000000000000 * 333752462382801674551679529044 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((333752462382801674551679529044 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5357506648225348657910639018801216000000000000000000000000 cm42_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_3_1_0 :
    ∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 1475624902578001558059447495770312000000000000000000000000 := by
  decide +kernel

theorem cb42_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((1475624902578001558059447495770312000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1475624902578001558059447495770312000000000000000000000000 cm42_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_4_0_0 :
    ∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 12196246571669230514732292728444000000000000000000000000 := by
  decide +kernel

theorem cb42_4_0_0 :
    ((∑ w, mu3 1 1 (⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((12196246571669230514732292728444000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12196246571669230514732292728444000000000000000000000000 cm42_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6732902965010242602866614361010308000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6732902965010242602866614361010308000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6732902965010242602866614361010308000000000000000000000000 gm42_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22157434258595038828145859196752184000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22157434258595038828145859196752184000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22157434258595038828145859196752184000000000000000000000000 gm42_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1387592563356563175470707634937536000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1387592563356563175470707634937536000000000000000000000000 * 5554253608295890819263026 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-45 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5554253608295890819263026 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1387592563356563175470707634937536000000000000000000000000 gm42_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm42_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg42 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (42 : Fin 88)),
            if yzBoundary 0 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((42 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((42 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((18169277068691921489687129411176873854278682153995220213698167680000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp42 (fun b ↦
    if yzBoundary 0 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(42 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(42 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(42 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ42]
  rw [kzero _ gm42_3]
  rw [kzero _ gm42_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb42_2_2_0 (add_le_add cb42_3_1_0 (add_le_add cb42_4_0_0 (add_le_add gb42_0 (add_le_add gb42_1 gb42_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp43 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ43 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm43_3_1_0 :
    ∑ w, mu3 1 1 (⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 165228389875217262118305587261400000000000000000000000000 := by
  decide +kernel

theorem cb43_3_1_0 :
    ((∑ w, mu3 1 1 (⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((165228389875217262118305587261400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 165228389875217262118305587261400000000000000000000000000 cm43_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm43_4_0_0 :
    ∑ w, mu3 1 1 (⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w = 6721294725925393914383631459732000000000000000000000000 := by
  decide +kernel

theorem cb43_4_0_0 :
    ((∑ w, mu3 1 1 (⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 (⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1))) w : ℚ) : ℝ)) ≤
      ((6721294725925393914383631459732000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6721294725925393914383631459732000000000000000000000000 cm43_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 463138925998000131521616368540268000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 1 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((463138925998000131521616368540268000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 463138925998000131521616368540268000000000000000000000000 gm43_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 304631830848708263317694412738600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 1 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((304631830848708263317694412738600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 304631830848708263317694412738600000000000000000000000000 gm43_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 1 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm43_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 1 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm43_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 1 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg43 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 (43 : Fin 88)),
            if yzBoundary 0 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr ((43 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr ((43 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((325682287252062563162089541992662181347649619830668000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp43 (fun b ↦
    if yzBoundary 0 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
      ((∑ w, mu3 1 1 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 1 1 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(43 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(43 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) from rfl)]
  rw [hJ43]
  rw [kzero _ gm43_2]
  rw [kzero _ gm43_3]
  rw [kzero _ gm43_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb43_3_1_0 (add_le_add cb43_4_0_0 (add_le_add gb43_0 gb43_1))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((268670311225201368818294824816096903326475480751573896329066049242000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg22 (add_le_add L3K.reg23 (add_le_add L3K.reg24 (add_le_add L3K.reg25 (add_le_add L3K.reg26 (add_le_add L3K.reg27 (add_le_add L3K.reg28 (add_le_add L3K.reg29 (add_le_add L3K.reg30 (add_le_add L3K.reg31 (add_le_add L3K.reg32 (add_le_add L3K.reg33 (add_le_add L3K.reg34 (add_le_add L3K.reg35 (add_le_add L3K.reg36 (add_le_add L3K.reg37 (add_le_add L3K.reg38 (add_le_add L3K.reg39 (add_le_add L3K.reg40 (add_le_add L3K.reg41 (add_le_add L3K.reg42 L3K.reg43))))))))))))))))))))) (le_of_eq (by push_cast; ring))
