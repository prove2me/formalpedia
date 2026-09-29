-- Prove2me | solution 1 for mme_released_recursive_stage_region0_compat2_s1_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T13:04:30.380243+00:00
-- url     : https://prove2.me/submissions/6ac4d77b-644d-44b8-9f9e-63cf4a74452c

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat9
import Theorems.Thm_mme_released_recursive_level3_compat10
import Theorems.Thm_mme_released_recursive_level3_compat11
import Theorems.Thm_mme_released_recursive_level3_compat12
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

theorem hsp66 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ66 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm66_0_2_2 :
    ∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 346213434962757992436734880026510000000000000000000000000 := by
  decide +kernel

theorem cb66_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((346213434962757992436734880026510000000000000000000000000 * 302996768180813447501777813721 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((302996768180813447501777813721 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 346213434962757992436734880026510000000000000000000000000 cm66_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_0_3_1 :
    ∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 80517728018959829968142406175580000000000000000000000000 := by
  decide +kernel

theorem cb66_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(66 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((80517728018959829968142406175580000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 80517728018959829968142406175580000000000000000000000000 cm66_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_0_4_0 :
    ∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 755230020756004804423250871660000000000000000000000000 := by
  decide +kernel

theorem cb66_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(66 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((755230020756004804423250871660000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 755230020756004804423250871660000000000000000000000000 cm66_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_2_0_2 :
    ∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 755230020756004804423250871660000000000000000000000000 := by
  decide +kernel

theorem cb66_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((755230020756004804423250871660000000000000000000000000 * 345312944091837466982261437023 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 1 else if k.val = 2 then -1 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((345312944091837466982261437023 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 755230020756004804423250871660000000000000000000000000 cm66_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 435686429262212337409991145116640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((435686429262212337409991145116640000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 435686429262212337409991145116640000000000000000000000000 gm66_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1415429080409320493463028801847820000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1415429080409320493463028801847820000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1415429080409320493463028801847820000000000000000000000000 gm66_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 89472994299454344973256265090130000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((89472994299454344973256265090130000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 89472994299454344973256265090130000000000000000000000000 gm66_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm66_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg66 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (66 : Fin 88)),
            if yzBoundary 1 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((66 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((66 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1142073655126138849311236503742686770950723715687573381342901300000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp66 (fun b ↦
    if yzBoundary 1 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ66]
  rw [kzero _ gm66_3]
  rw [kzero _ gm66_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb66_0_2_2 (add_le_add cb66_0_3_1 (add_le_add cb66_0_4_0 (add_le_add cb66_2_0_2 (add_le_add gb66_0 (add_le_add gb66_1 gb66_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp67 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ67 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm67_0_3_1 :
    ∑ w, mu3 0 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 806771532479672274577856057596584000000000000000000000000 := by
  decide +kernel

theorem cb67_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((806771532479672274577856057596584000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 806771532479672274577856057596584000000000000000000000000 cm67_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm67_0_4_0 :
    ∑ w, mu3 0 2 (⟨(67 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 31065394463832832554504230046744000000000000000000000000 := by
  decide +kernel

theorem cb67_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(67 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(67 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((31065394463832832554504230046744000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31065394463832832554504230046744000000000000000000000000 cm67_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2310250167561723638681495769953256000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2310250167561723638681495769953256000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2310250167561723638681495769953256000000000000000000000000 gm67_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1534544029545884196658143942403416000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1534544029545884196658143942403416000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1534544029545884196658143942403416000000000000000000000000 gm67_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm67_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm67_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg67 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (67 : Fin 88)),
            if yzBoundary 1 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((67 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((67 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1622876280619138222789767514584237737393542222126068000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp67 (fun b ↦
    if yzBoundary 1 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ67]
  rw [kzero _ gm67_2]
  rw [kzero _ gm67_3]
  rw [kzero _ gm67_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb67_0_3_1 (add_le_add cb67_0_4_0 (add_le_add gb67_0 gb67_1))) (le_of_eq (by push_cast; ring)))

theorem hsp68 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ68 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm68_0_0_4 :
    ∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3972864274738291164469049425140000000000000000000000000 := by
  decide +kernel

theorem cb68_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(68 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3972864274738291164469049425140000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3972864274738291164469049425140000000000000000000000000 cm68_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_0_1_3 :
    ∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 153734806571978587259052779747904000000000000000000000000 := by
  decide +kernel

theorem cb68_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(68 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((153734806571978587259052779747904000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 153734806571978587259052779747904000000000000000000000000 cm68_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_1_0_3 :
    ∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 819334293017842917954451840198644000000000000000000000000 := by
  decide +kernel

theorem cb68_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(68 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((819334293017842917954451840198644000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 819334293017842917954451840198644000000000000000000000000 cm68_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_2_0_2 :
    ∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5067859517023775235754026330628312000000000000000000000000 := by
  decide +kernel

theorem cb68_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5067859517023775235754026330628312000000000000000000000000 * 384190181476034521557245087253 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((384190181476034521557245087253 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5067859517023775235754026330628312000000000000000000000000 cm68_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_3_0_1 :
    ∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 153734806571978587259052779747904000000000000000000000000 := by
  decide +kernel

theorem cb68_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((153734806571978587259052779747904000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 153734806571978587259052779747904000000000000000000000000 cm68_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3972864274738291164469049425140000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3972864274738291164469049425140000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3972864274738291164469049425140000000000000000000000000 gm68_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 819334293017842917954451840198644000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((819334293017842917954451840198644000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 819334293017842917954451840198644000000000000000000000000 gm68_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5067859517023775235754026330628312000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5067859517023775235754026330628312000000000000000000000000 * 15742154329414862340054273714 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15742154329414862340054273714 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5067859517023775235754026330628312000000000000000000000000 gm68_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm68_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg68 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (68 : Fin 88)),
            if yzBoundary 1 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((68 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((68 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3375761099918573828407681983843523005938266806615416962697208240000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp68 (fun b ↦
    if yzBoundary 1 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ68]
  rw [kzero _ gm68_3]
  rw [kzero _ gm68_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb68_0_0_4 (add_le_add cb68_0_1_3 (add_le_add cb68_1_0_3 (add_le_add cb68_2_0_2 (add_le_add cb68_3_0_1 (add_le_add gb68_0 (add_le_add gb68_1 gb68_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp69 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ69 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm69_0_1_3 :
    ∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84926287934730305848477888997760000000000000000000000000 := by
  decide +kernel

theorem cb69_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(69 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84926287934730305848477888997760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 84926287934730305848477888997760000000000000000000000000 cm69_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_0_2_2 :
    ∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 571457183921737781533206750807020000000000000000000000000 := by
  decide +kernel

theorem cb69_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((571457183921737781533206750807020000000000000000000000000 * 416953379562345900132780711739 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416953379562345900132780711739 : ℚ)/10^30) mme_released_recursive_level3_compat10.1 571457183921737781533206750807020000000000000000000000000 cm69_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_1_0_3 :
    ∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 624341045846781583204004738658110000000000000000000000000 := by
  decide +kernel

theorem cb69_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(69 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((624341045846781583204004738658110000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.1 624341045846781583204004738658110000000000000000000000000 cm69_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_2_0_2 :
    ∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 8314385937398678859492290733285590000000000000000000000000 := by
  decide +kernel

theorem cb69_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((8314385937398678859492290733285590000000000000000000000000 * 434242441048092939007226722529 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((434242441048092939007226722529 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.1 8314385937398678859492290733285590000000000000000000000000 cm69_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_3_0_1 :
    ∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 571457183921737781533206750807020000000000000000000000000 := by
  decide +kernel

theorem cb69_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(69 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(69 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((571457183921737781533206750807020000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.1 571457183921737781533206750807020000000000000000000000000 cm69_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 709267333781511889052482627655870000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((709267333781511889052482627655870000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.1 709267333781511889052482627655870000000000000000000000000 gm69_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 24461971581822561644344310621537110000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((24461971581822561644344310621537110000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.1 24461971581822561644344310621537110000000000000000000000000 gm69_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 16147585644423882784852019888251520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((16147585644423882784852019888251520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.1 16147585644423882784852019888251520000000000000000000000000 gm69_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm69_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg69 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (69 : Fin 88)),
            if yzBoundary 1 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((69 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((69 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((21692207470781105780771533488906834286271804904253170149293016620000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp69 (fun b ↦
    if yzBoundary 1 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ69]
  rw [kzero _ gm69_3]
  rw [kzero _ gm69_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb69_0_1_3 (add_le_add cb69_0_2_2 (add_le_add cb69_1_0_3 (add_le_add cb69_2_0_2 (add_le_add cb69_3_0_1 (add_le_add gb69_0 (add_le_add gb69_1 gb69_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp70 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ70 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm70_0_2_2 :
    ∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 761642177609474226288463424443380000000000000000000000000 := by
  decide +kernel

theorem cb70_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(70 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((761642177609474226288463424443380000000000000000000000000 * 250262490893430709596781766165 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((250262490893430709596781766165 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 761642177609474226288463424443380000000000000000000000000 cm70_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_0_3_1 :
    ∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 106044303088642743106615152971820000000000000000000000000 := by
  decide +kernel

theorem cb70_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((106044303088642743106615152971820000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106044303088642743106615152971820000000000000000000000000 cm70_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_2_0_2 :
    ∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 808839386520025462023402833857380000000000000000000000000 := by
  decide +kernel

theorem cb70_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(70 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((808839386520025462023402833857380000000000000000000000000 * 425435311474830418946085672499 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (15 : Int) else if k.val = 1 then -3 else if k.val = 2 then -5 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((425435311474830418946085672499 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 808839386520025462023402833857380000000000000000000000000 cm70_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_3_0_1 :
    ∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 106044303088642743106615152971820000000000000000000000000 := by
  decide +kernel

theorem cb70_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((106044303088642743106615152971820000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106044303088642743106615152971820000000000000000000000000 cm70_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13114509519732627818852397736936740000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13114509519732627818852397736936740000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13114509519732627818852397736936740000000000000000000000000 gm70_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 44169286356055553367261974220182880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((44169286356055553367261974220182880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 44169286356055553367261974220182880000000000000000000000000 gm70_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11544027955603128130540531478635980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11544027955603128130540531478635980000000000000000000000000 * 181581830031593861389506768085 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181581830031593861389506768085 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11544027955603128130540531478635980000000000000000000000000 gm70_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm70_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg70 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (70 : Fin 88)),
            if yzBoundary 1 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((70 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((70 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((33393729951435038232631909381262157789821569826548257196468444920000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp70 (fun b ↦
    if yzBoundary 1 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ70]
  rw [kzero _ gm70_3]
  rw [kzero _ gm70_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb70_0_2_2 (add_le_add cb70_0_3_1 (add_le_add cb70_2_0_2 (add_le_add cb70_3_0_1 (add_le_add gb70_0 (add_le_add gb70_1 gb70_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp71 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ71 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm71_0_3_1 :
    ∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 931134997410157196366327208691265000000000000000000000000 := by
  decide +kernel

theorem cb71_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((931134997410157196366327208691265000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 931134997410157196366327208691265000000000000000000000000 cm71_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm71_0_4_0 :
    ∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25045615351170455003008195866959000000000000000000000000 := by
  decide +kernel

theorem cb71_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25045615351170455003008195866959000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25045615351170455003008195866959000000000000000000000000 cm71_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm71_3_0_1 :
    ∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25045615351170455003008195866959000000000000000000000000 := by
  decide +kernel

theorem cb71_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(71 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(71 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25045615351170455003008195866959000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25045615351170455003008195866959000000000000000000000000 cm71_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 38430056446335735721445991804133041000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((38430056446335735721445991804133041000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38430056446335735721445991804133041000000000000000000000000 gm71_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37498921448925578525079664595441776000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37498921448925578525079664595441776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37498921448925578525079664595441776000000000000000000000000 gm71_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm71_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm71_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg71 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (71 : Fin 88)),
            if yzBoundary 1 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((71 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((71 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((26655045572203219081732756103049473079261275397293837000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp71 (fun b ↦
    if yzBoundary 1 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ71]
  rw [kzero _ gm71_2]
  rw [kzero _ gm71_3]
  rw [kzero _ gm71_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb71_0_3_1 (add_le_add cb71_0_4_0 (add_le_add cb71_3_0_1 (add_le_add gb71_0 gb71_1)))) (le_of_eq (by push_cast; ring)))

theorem hsp72 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ72 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm72_0_2_2 :
    ∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 11958069195722864178737691889236000000000000000000000000 := by
  decide +kernel

theorem cb72_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(72 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((11958069195722864178737691889236000000000000000000000000 * 158487213503086856748621094 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -6 else if k.val = 2 then 2 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((158487213503086856748621094 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11958069195722864178737691889236000000000000000000000000 cm72_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_2_0_2 :
    ∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5251144889720533980071960781234756000000000000000000000000 := by
  decide +kernel

theorem cb72_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(72 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5251144889720533980071960781234756000000000000000000000000 * 335894349997483853900094213913 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((335894349997483853900094213913 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5251144889720533980071960781234756000000000000000000000000 cm72_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_3_0_1 :
    ∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1348456003270473637582619495705220000000000000000000000000 := by
  decide +kernel

theorem cb72_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(72 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1348456003270473637582619495705220000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1348456003270473637582619495705220000000000000000000000000 cm72_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_4_0_0 :
    ∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 11958069195722864178737691889236000000000000000000000000 := by
  decide +kernel

theorem cb72_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((11958069195722864178737691889236000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11958069195722864178737691889236000000000000000000000000 cm72_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6697180148984952445672968567747084000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6697180148984952445672968567747084000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6697180148984952445672968567747084000000000000000000000000 gm72_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21619828877654560934497967985022140000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21619828877654560934497967985022140000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21619828877654560934497967985022140000000000000000000000000 gm72_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1446035259264418465601007786512328000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1446035259264418465601007786512328000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1446035259264418465601007786512328000000000000000000000000 gm72_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm72_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg72 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (72 : Fin 88)),
            if yzBoundary 1 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((72 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((72 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17684233702187160391843471263706843686691536839576065352202909108000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp72 (fun b ↦
    if yzBoundary 1 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ72]
  rw [kzero _ gm72_3]
  rw [kzero _ gm72_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb72_0_2_2 (add_le_add cb72_2_0_2 (add_le_add cb72_3_0_1 (add_le_add cb72_4_0_0 (add_le_add gb72_0 (add_le_add gb72_1 gb72_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp73 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ73 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm73_2_0_2 :
    ∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 142733181620865038737615539318520000000000000000000000000 := by
  decide +kernel

theorem cb73_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(73 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((142733181620865038737615539318520000000000000000000000000 * 304707057047200127886278571794 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304707057047200127886278571794 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 142733181620865038737615539318520000000000000000000000000 cm73_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm73_3_0_1 :
    ∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 257387023813141652527029003371520000000000000000000000000 := by
  decide +kernel

theorem cb73_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(73 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((257387023813141652527029003371520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 257387023813141652527029003371520000000000000000000000000 cm73_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm73_4_0_0 :
    ∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 5809305748384875655355457309960000000000000000000000000 := by
  decide +kernel

theorem cb73_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((5809305748384875655355457309960000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5809305748384875655355457309960000000000000000000000000 cm73_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 142733181620865038737615539318520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((142733181620865038737615539318520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 142733181620865038737615539318520000000000000000000000000 gm73_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 257387023813141652527029003371520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((257387023813141652527029003371520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 257387023813141652527029003371520000000000000000000000000 gm73_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5809305748384875655355457309960000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5809305748384875655355457309960000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5809305748384875655355457309960000000000000000000000000 gm73_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm73_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg73 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (73 : Fin 88)),
            if yzBoundary 1 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((73 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((73 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((400305987452266580331410779133864366423904566431760399191852200000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp73 (fun b ↦
    if yzBoundary 1 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(73 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(73 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(73 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(73 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(73 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(73 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ73]
  rw [kzero _ gm73_3]
  rw [kzero _ gm73_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb73_2_0_2 (add_le_add cb73_3_0_1 (add_le_add cb73_4_0_0 (add_le_add gb73_0 (add_le_add gb73_1 gb73_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp74 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ74 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm74_3_0_1 :
    ∑ w, mu3 0 2 (⟨(74 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84487897829003799685109275746432000000000000000000000000 := by
  decide +kernel

theorem cb74_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(74 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(74 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84487897829003799685109275746432000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (74 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84487897829003799685109275746432000000000000000000000000 cm74_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm74_4_0_0 :
    ∑ w, mu3 0 2 (⟨(74 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25754514002091374842890724253568000000000000000000000000 := by
  decide +kernel

theorem cb74_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(74 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(74 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25754514002091374842890724253568000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (74 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25754514002091374842890724253568000000000000000000000000 cm74_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84487897829003799685109275746432000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb74_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84487897829003799685109275746432000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84487897829003799685109275746432000000000000000000000000 gm74_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25754514002091374842890724253568000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb74_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25754514002091374842890724253568000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25754514002091374842890724253568000000000000000000000000 gm74_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg74 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (74 : Fin 88)),
            if yzBoundary 1 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((74 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((74 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76414216938851977939355646566446373459645261268864000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp74 (fun b ↦
    if yzBoundary 1 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(74 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(74 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(74 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(74 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ74]
  rw [kzero _ gm74_2]
  rw [kzero _ gm74_3]
  rw [kzero _ gm74_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb74_3_0_1 (add_le_add cb74_4_0_0 (add_le_add gb74_0 gb74_1))) (le_of_eq (by push_cast; ring)))

theorem hsp75 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ75 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm75_0_0_4 :
    ∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 26498811842078523714467248002048000000000000000000000000 := by
  decide +kernel

theorem cb75_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((26498811842078523714467248002048000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26498811842078523714467248002048000000000000000000000000 cm75_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm75_0_1_3 :
    ∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84946570171962360509532751997952000000000000000000000000 := by
  decide +kernel

theorem cb75_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84946570171962360509532751997952000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84946570171962360509532751997952000000000000000000000000 cm75_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm75_1_0_3 :
    ∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84946570171962360509532751997952000000000000000000000000 := by
  decide +kernel

theorem cb75_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84946570171962360509532751997952000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84946570171962360509532751997952000000000000000000000000 cm75_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26498811842078523714467248002048000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb75_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26498811842078523714467248002048000000000000000000000000 * 203944572739024876231370163719 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((203944572739024876231370163719 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26498811842078523714467248002048000000000000000000000000 gm75_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg75 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (75 : Fin 88)),
            if yzBoundary 1 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((75 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((75 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((123165240085091034795605619246524047176153937560319898799286272000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp75 (fun b ↦
    if yzBoundary 1 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(75 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ75]
  rw [kzero _ gm75_0]
  rw [kzero _ gm75_1]
  rw [kzero _ gm75_3]
  rw [kzero _ gm75_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb75_0_0_4 (add_le_add cb75_0_1_3 (add_le_add cb75_1_0_3 gb75_2))) (le_of_eq (by push_cast; ring)))

theorem hsp76 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ76 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm76_0_0_4 :
    ∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 47148500442199917786727415068678000000000000000000000000 := by
  decide +kernel

theorem cb76_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((47148500442199917786727415068678000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 47148500442199917786727415068678000000000000000000000000 cm76_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_0_1_3 :
    ∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2018006204548620053245093983212114000000000000000000000000 := by
  decide +kernel

theorem cb76_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2018006204548620053245093983212114000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2018006204548620053245093983212114000000000000000000000000 cm76_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_0_2_2 :
    ∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1134197890408776305351178601719208000000000000000000000000 := by
  decide +kernel

theorem cb76_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(76 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1134197890408776305351178601719208000000000000000000000000 * 432510796031012744850205102731 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432510796031012744850205102731 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1134197890408776305351178601719208000000000000000000000000 cm76_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_1_0_3 :
    ∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1134197890408776305351178601719208000000000000000000000000 := by
  decide +kernel

theorem cb76_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1134197890408776305351178601719208000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1134197890408776305351178601719208000000000000000000000000 cm76_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm76_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 47148500442199917786727415068678000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((47148500442199917786727415068678000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 47148500442199917786727415068678000000000000000000000000 gm76_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2018006204548620053245093983212114000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2018006204548620053245093983212114000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2018006204548620053245093983212114000000000000000000000000 gm76_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm76_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg76 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (76 : Fin 88)),
            if yzBoundary 1 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((76 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((76 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2708175063555768806077497032275680979956502742148880920643922592000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp76 (fun b ↦
    if yzBoundary 1 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(76 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(76 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ76]
  rw [kzero _ gm76_0]
  rw [kzero _ gm76_3]
  rw [kzero _ gm76_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb76_0_0_4 (add_le_add cb76_0_1_3 (add_le_add cb76_0_2_2 (add_le_add cb76_1_0_3 (add_le_add gb76_1 gb76_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp77 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ77 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm77_0_0_4 :
    ∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 7098179432574057430564115055657000000000000000000000000 := by
  decide +kernel

theorem cb77_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((7098179432574057430564115055657000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.1 7098179432574057430564115055657000000000000000000000000 cm77_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_0_1_3 :
    ∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1458514230003070448213641285206144000000000000000000000000 := by
  decide +kernel

theorem cb77_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1458514230003070448213641285206144000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.1 1458514230003070448213641285206144000000000000000000000000 cm77_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_0_2_2 :
    ∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 9016827988745247560367157700741355000000000000000000000000 := by
  decide +kernel

theorem cb77_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((9016827988745247560367157700741355000000000000000000000000 * 384191613525569409591347845924 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((384191613525569409591347845924 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.1 9016827988745247560367157700741355000000000000000000000000 cm77_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_0_3_1 :
    ∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 274662759426081169957636898996844000000000000000000000000 := by
  decide +kernel

theorem cb77_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((274662759426081169957636898996844000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.1 274662759426081169957636898996844000000000000000000000000 cm77_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_1_0_3 :
    ∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 274662759426081169957636898996844000000000000000000000000 := by
  decide +kernel

theorem cb77_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((274662759426081169957636898996844000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.1 274662759426081169957636898996844000000000000000000000000 cm77_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7098179432574057430564115055657000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7098179432574057430564115055657000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.1 7098179432574057430564115055657000000000000000000000000 gm77_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1458514230003070448213641285206144000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1458514230003070448213641285206144000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.1 1458514230003070448213641285206144000000000000000000000000 gm77_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9016827988745247560367157700741355000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9016827988745247560367157700741355000000000000000000000000 * 15741724371825556202478018761 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 0 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15741724371825556202478018761 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.1 9016827988745247560367157700741355000000000000000000000000 gm77_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm77_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg77 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (77 : Fin 88)),
            if yzBoundary 1 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((77 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((77 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((6008823602053922503334785231019423991549551188392135418642763229000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp77 (fun b ↦
    if yzBoundary 1 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ77]
  rw [kzero _ gm77_3]
  rw [kzero _ gm77_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb77_0_0_4 (add_le_add cb77_0_1_3 (add_le_add cb77_0_2_2 (add_le_add cb77_0_3_1 (add_le_add cb77_1_0_3 (add_le_add gb77_0 (add_le_add gb77_1 gb77_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp78 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ78 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm78_0_2_2 :
    ∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 192490588332864267105883981661496000000000000000000000000 := by
  decide +kernel

theorem cb78_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((192490588332864267105883981661496000000000000000000000000 * 304730053759554273517104376303 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304730053759554273517104376303 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 192490588332864267105883981661496000000000000000000000000 cm78_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm78_0_3_1 :
    ∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 346987272401321071852157357525328000000000000000000000000 := by
  decide +kernel

theorem cb78_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((346987272401321071852157357525328000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 346987272401321071852157357525328000000000000000000000000 cm78_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm78_0_4_0 :
    ∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 7837072649275841193958660813176000000000000000000000000 := by
  decide +kernel

theorem cb78_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((7837072649275841193958660813176000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7837072649275841193958660813176000000000000000000000000 cm78_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 192490588332864267105883981661496000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((192490588332864267105883981661496000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 192490588332864267105883981661496000000000000000000000000 gm78_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 346987272401321071852157357525328000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((346987272401321071852157357525328000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 346987272401321071852157357525328000000000000000000000000 gm78_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7837072649275841193958660813176000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7837072649275841193958660813176000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7837072649275841193958660813176000000000000000000000000 gm78_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm78_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg78 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (78 : Fin 88)),
            if yzBoundary 1 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((78 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((78 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((539684166441204808412030287376971992502658892157071031011248160000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp78 (fun b ↦
    if yzBoundary 1 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(78 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(78 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(78 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(78 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(78 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(78 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ78]
  rw [kzero _ gm78_3]
  rw [kzero _ gm78_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb78_0_2_2 (add_le_add cb78_0_3_1 (add_le_add cb78_0_4_0 (add_le_add gb78_0 (add_le_add gb78_1 gb78_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp79 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ79 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm79_0_3_1 :
    ∑ w, mu3 0 2 (⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84464484824829452816880987318900000000000000000000000000 := by
  decide +kernel

theorem cb79_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84464484824829452816880987318900000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84464484824829452816880987318900000000000000000000000000 cm79_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm79_0_4_0 :
    ∑ w, mu3 0 2 (⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25817136173108185803119012681100000000000000000000000000 := by
  decide +kernel

theorem cb79_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25817136173108185803119012681100000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25817136173108185803119012681100000000000000000000000000 cm79_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84464484824829452816880987318900000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84464484824829452816880987318900000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84464484824829452816880987318900000000000000000000000000 gm79_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25817136173108185803119012681100000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25817136173108185803119012681100000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25817136173108185803119012681100000000000000000000000000 gm79_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm79_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm79_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg79 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (79 : Fin 88)),
            if yzBoundary 1 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((79 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((79 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76441394662300936418036302595072409427311649302060000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp79 (fun b ↦
    if yzBoundary 1 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(79 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ79]
  rw [kzero _ gm79_2]
  rw [kzero _ gm79_3]
  rw [kzero _ gm79_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb79_0_3_1 (add_le_add cb79_0_4_0 (add_le_add gb79_0 gb79_1))) (le_of_eq (by push_cast; ring)))

theorem hsp80 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ80 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm80_0_0_4 :
    ∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 41804542829927110005384961570000000000000000000000000000 := by
  decide +kernel

theorem cb80_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((41804542829927110005384961570000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 41804542829927110005384961570000000000000000000000000000 cm80_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_0_1_3 :
    ∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1006472041946385489324541815968000000000000000000000000000 := by
  decide +kernel

theorem cb80_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1006472041946385489324541815968000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1006472041946385489324541815968000000000000000000000000000 cm80_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_1_0_3 :
    ∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1795998183061080661170073222462000000000000000000000000000 := by
  decide +kernel

theorem cb80_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1795998183061080661170073222462000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1795998183061080661170073222462000000000000000000000000000 cm80_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_2_0_2 :
    ∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 1006472041946385489324541815968000000000000000000000000000 := by
  decide +kernel

theorem cb80_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((1006472041946385489324541815968000000000000000000000000000 * 432668421183174632706056166718 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432668421183174632706056166718 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1006472041946385489324541815968000000000000000000000000000 cm80_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm80_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 41804542829927110005384961570000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((41804542829927110005384961570000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 41804542829927110005384961570000000000000000000000000000 gm80_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1795998183061080661170073222462000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1795998183061080661170073222462000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1795998183061080661170073222462000000000000000000000000000 gm80_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm80_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg80 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (80 : Fin 88)),
            if yzBoundary 1 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((80 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((80 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2406969705418230674946723496890232428951032743361292889841248000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp80 (fun b ↦
    if yzBoundary 1 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ80]
  rw [kzero _ gm80_0]
  rw [kzero _ gm80_3]
  rw [kzero _ gm80_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb80_0_0_4 (add_le_add cb80_0_1_3 (add_le_add cb80_1_0_3 (add_le_add cb80_2_0_2 (add_le_add gb80_1 gb80_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp81 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ81 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm81_0_2_2 :
    ∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 2033127618580756897478290594585392000000000000000000000000 := by
  decide +kernel

theorem cb81_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((2033127618580756897478290594585392000000000000000000000000 * 315890471613997859826543698982 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((315890471613997859826543698982 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2033127618580756897478290594585392000000000000000000000000 cm81_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_0_3_1 :
    ∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 505701020543803190246041262610288000000000000000000000000 := by
  decide +kernel

theorem cb81_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(81 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((505701020543803190246041262610288000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 505701020543803190246041262610288000000000000000000000000 cm81_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_0_4_0 :
    ∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 4631075929028604590969935215936000000000000000000000000 := by
  decide +kernel

theorem cb81_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(81 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((4631075929028604590969935215936000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4631075929028604590969935215936000000000000000000000000 cm81_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_2_0_2 :
    ∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 4631075929028604590969935215936000000000000000000000000 := by
  decide +kernel

theorem cb81_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((4631075929028604590969935215936000000000000000000000000 * 347373627686919124679530871049 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((347373627686919124679530871049 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4631075929028604590969935215936000000000000000000000000 cm81_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2600460323619879589840687925982864000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2600460323619879589840687925982864000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2600460323619879589840687925982864000000000000000000000000 gm81_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8368248379564111010298643014992112000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8368248379564111010298643014992112000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8368248379564111010298643014992112000000000000000000000000 gm81_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 567332705039122692362397331397472000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((567332705039122692362397331397472000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 567332705039122692362397331397472000000000000000000000000 gm81_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm81_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg81 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (81 : Fin 88)),
            if yzBoundary 1 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((81 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((81 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((6794807363046898656416542507864837077222936048913066785542096112000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp81 (fun b ↦
    if yzBoundary 1 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ81]
  rw [kzero _ gm81_3]
  rw [kzero _ gm81_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb81_0_2_2 (add_le_add cb81_0_3_1 (add_le_add cb81_0_4_0 (add_le_add cb81_2_0_2 (add_le_add gb81_0 (add_le_add gb81_1 gb81_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp82 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ82 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm82_0_3_1 :
    ∑ w, mu3 0 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 726097667590188395551673895004032000000000000000000000000 := by
  decide +kernel

theorem cb82_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((726097667590188395551673895004032000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 726097667590188395551673895004032000000000000000000000000 cm82_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm82_0_4_0 :
    ∑ w, mu3 0 2 (⟨(82 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 29170577582997481982977337380160000000000000000000000000 := by
  decide +kernel

theorem cb82_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(82 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(82 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((29170577582997481982977337380160000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29170577582997481982977337380160000000000000000000000000 cm82_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2043498199623428820113022662619840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2043498199623428820113022662619840000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2043498199623428820113022662619840000000000000000000000000 gm82_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1346571109616237906544326104995968000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1346571109616237906544326104995968000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1346571109616237906544326104995968000000000000000000000000 gm82_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm82_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm82_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg82 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (82 : Fin 88)),
            if yzBoundary 1 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((82 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((82 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1436664519155263828947960833739985627070103909927248000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp82 (fun b ↦
    if yzBoundary 1 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ82]
  rw [kzero _ gm82_2]
  rw [kzero _ gm82_3]
  rw [kzero _ gm82_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb82_0_3_1 (add_le_add cb82_0_4_0 (add_le_add gb82_0 gb82_1))) (le_of_eq (by push_cast; ring)))

theorem hsp83 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ83 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm83_0_0_4 :
    ∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 3892148027783264932190633907824000000000000000000000000 := by
  decide +kernel

theorem cb83_0_0_4 :
    ((∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((3892148027783264932190633907824000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3892148027783264932190633907824000000000000000000000000 cm83_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_0_1_3 :
    ∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 150590287656107205727667408593632000000000000000000000000 := by
  decide +kernel

theorem cb83_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((150590287656107205727667408593632000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 150590287656107205727667408593632000000000000000000000000 cm83_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_1_0_3 :
    ∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 805975522306334257913193838458784000000000000000000000000 := by
  decide +kernel

theorem cb83_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((805975522306334257913193838458784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 805975522306334257913193838458784000000000000000000000000 cm83_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_2_0_2 :
    ∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 4983540998580237818170948119039760000000000000000000000000 := by
  decide +kernel

theorem cb83_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((4983540998580237818170948119039760000000000000000000000000 * 383795277689744236506165497633 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((383795277689744236506165497633 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4983540998580237818170948119039760000000000000000000000000 cm83_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_3_0_1 :
    ∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 150590287656107205727667408593632000000000000000000000000 := by
  decide +kernel

theorem cb83_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((150590287656107205727667408593632000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 150590287656107205727667408593632000000000000000000000000 cm83_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3892148027783264932190633907824000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3892148027783264932190633907824000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3892148027783264932190633907824000000000000000000000000 gm83_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 805975522306334257913193838458784000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((805975522306334257913193838458784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 805975522306334257913193838458784000000000000000000000000 gm83_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4983540998580237818170948119039760000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4983540998580237818170948119039760000000000000000000000000 * 15886109591510318200123186980 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15886109591510318200123186980 : ℚ)/10^30) mme_released_recursive_level3_compat11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4983540998580237818170948119039760000000000000000000000000 gm83_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm83_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg83 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (83 : Fin 88)),
            if yzBoundary 1 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((83 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((83 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3317910368276571576122838169713219678435476640923369004742551408000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp83 (fun b ↦
    if yzBoundary 1 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ83]
  rw [kzero _ gm83_3]
  rw [kzero _ gm83_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb83_0_0_4 (add_le_add cb83_0_1_3 (add_le_add cb83_1_0_3 (add_le_add cb83_2_0_2 (add_le_add cb83_3_0_1 (add_le_add gb83_0 (add_le_add gb83_1 gb83_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp84 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ84 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm84_0_1_3 :
    ∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 74244619588388573932882743929600000000000000000000000000 := by
  decide +kernel

theorem cb84_0_1_3 :
    ((∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((74244619588388573932882743929600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.1 74244619588388573932882743929600000000000000000000000000 cm84_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_0_2_2 :
    ∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 499396100591064448020977315229760000000000000000000000000 := by
  decide +kernel

theorem cb84_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((499396100591064448020977315229760000000000000000000000000 * 417460321644142474476887223059 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then 4 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((417460321644142474476887223059 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.1 499396100591064448020977315229760000000000000000000000000 cm84_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_1_0_3 :
    ∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 548768205292322505074196421677760000000000000000000000000 := by
  decide +kernel

theorem cb84_1_0_3 :
    ((∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((548768205292322505074196421677760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.1 548768205292322505074196421677760000000000000000000000000 cm84_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_2_0_2 :
    ∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 7305756266674255299857197831131680000000000000000000000000 := by
  decide +kernel

theorem cb84_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((7305756266674255299857197831131680000000000000000000000000 * 433849005008211281695666995480 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((433849005008211281695666995480 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.1 7305756266674255299857197831131680000000000000000000000000 cm84_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_3_0_1 :
    ∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 499396100591064448020977315229760000000000000000000000000 := by
  decide +kernel

theorem cb84_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((499396100591064448020977315229760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.1 499396100591064448020977315229760000000000000000000000000 cm84_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 623012824880711079007079165607360000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((623012824880711079007079165607360000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.1 623012824880711079007079165607360000000000000000000000000 gm84_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21498386309921335579051943519162880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21498386309921335579051943519162880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.1 21498386309921335579051943519162880000000000000000000000000 gm84_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14192630043247080279194745688031200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14192630043247080279194745688031200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.1 14192630043247080279194745688031200000000000000000000000000 gm84_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm84_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg84 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (84 : Fin 88)),
            if yzBoundary 1 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((84 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((84 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((19057613583346285579798028866666046799141425911726714522775312160000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp84 (fun b ↦
    if yzBoundary 1 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ84]
  rw [kzero _ gm84_3]
  rw [kzero _ gm84_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb84_0_1_3 (add_le_add cb84_0_2_2 (add_le_add cb84_1_0_3 (add_le_add cb84_2_0_2 (add_le_add cb84_3_0_1 (add_le_add gb84_0 (add_le_add gb84_1 gb84_2))))))) (le_of_eq (by push_cast; ring)))

theorem hsp85 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ85 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm85_0_2_2 :
    ∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 656731232598558504124398317161024000000000000000000000000 := by
  decide +kernel

theorem cb85_0_2_2 :
    ((∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((656731232598558504124398317161024000000000000000000000000 * 252451254805585744960409095877 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -3 else if k.val = 2 then -8 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((252451254805585744960409095877 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 656731232598558504124398317161024000000000000000000000000 cm85_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_0_3_1 :
    ∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 92103144124455254399163157127616000000000000000000000000 := by
  decide +kernel

theorem cb85_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((92103144124455254399163157127616000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92103144124455254399163157127616000000000000000000000000 cm85_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_2_0_2 :
    ∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 706255564683359297680597067196224000000000000000000000000 := by
  decide +kernel

theorem cb85_2_0_2 :
    ((∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((706255564683359297680597067196224000000000000000000000000 * 424739979056874332973384333761 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424739979056874332973384333761 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 706255564683359297680597067196224000000000000000000000000 cm85_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_3_0_1 :
    ∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 92103144124455254399163157127616000000000000000000000000 := by
  decide +kernel

theorem cb85_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((92103144124455254399163157127616000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92103144124455254399163157127616000000000000000000000000 cm85_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11367308468874591098161463129604512000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11367308468874591098161463129604512000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11367308468874591098161463129604512000000000000000000000000 gm85_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 38291343848557444490334747426535744000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((38291343848557444490334747426535744000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38291343848557444490334747426535744000000000000000000000000 gm85_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10004321671592673296356467745247264000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10004321671592673296356467745247264000000000000000000000000 * 181358717068914833191911184171 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181358717068914833191911184171 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10004321671592673296356467745247264000000000000000000000000 gm85_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm85_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg85 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (85 : Fin 88)),
            if yzBoundary 1 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((85 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((85 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((28949357638816867811010353833113779787955772123411985164956252096000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp85 (fun b ↦
    if yzBoundary 1 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ85]
  rw [kzero _ gm85_3]
  rw [kzero _ gm85_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb85_0_2_2 (add_le_add cb85_0_3_1 (add_le_add cb85_2_0_2 (add_le_add cb85_3_0_1 (add_le_add gb85_0 (add_le_add gb85_1 gb85_2)))))) (le_of_eq (by push_cast; ring)))

theorem hsp86 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ86 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm86_0_3_1 :
    ∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 806204796961804173282953304746892000000000000000000000000 := by
  decide +kernel

theorem cb86_0_3_1 :
    ((∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((806204796961804173282953304746892000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 806204796961804173282953304746892000000000000000000000000 cm86_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm86_0_4_0 :
    ∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 21344626718667803911298727202491000000000000000000000000 := by
  decide +kernel

theorem cb86_0_4_0 :
    ((∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((21344626718667803911298727202491000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21344626718667803911298727202491000000000000000000000000 cm86_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm86_3_0_1 :
    ∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 21344626718667803911298727202491000000000000000000000000 := by
  decide +kernel

theorem cb86_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((21344626718667803911298727202491000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21344626718667803911298727202491000000000000000000000000 cm86_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32917442295798075498507701272797509000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32917442295798075498507701272797509000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32917442295798075498507701272797509000000000000000000000000 gm86_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32111237498836271325224747968050617000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32111237498836271325224747968050617000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32111237498836271325224747968050617000000000000000000000000 gm86_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm86_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm86_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg86 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (86 : Fin 88)),
            if yzBoundary 1 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((86 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((86 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((22831427286407278358012562799037319990761904289931447000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp86 (fun b ↦
    if yzBoundary 1 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(86 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ86]
  rw [kzero _ gm86_2]
  rw [kzero _ gm86_3]
  rw [kzero _ gm86_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb86_0_3_1 (add_le_add cb86_0_4_0 (add_le_add cb86_3_0_1 (add_le_add gb86_0 gb86_1)))) (le_of_eq (by push_cast; ring)))

theorem hsp87 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ87 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm87_3_0_1 :
    ∑ w, mu3 0 2 (⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 84581398588867641271830025748784000000000000000000000000 := by
  decide +kernel

theorem cb87_3_0_1 :
    ((∑ w, mu3 0 2 (⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((84581398588867641271830025748784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84581398588867641271830025748784000000000000000000000000 cm87_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm87_4_0_0 :
    ∑ w, mu3 0 2 (⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w = 25044250885923669036169974251216000000000000000000000000 := by
  decide +kernel

theorem cb87_4_0_0 :
    ((∑ w, mu3 0 2 (⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 (⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0))) w : ℚ) : ℝ)) ≤
      ((25044250885923669036169974251216000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 25044250885923669036169974251216000000000000000000000000 cm87_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84581398588867641271830025748784000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 0 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84581398588867641271830025748784000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84581398588867641271830025748784000000000000000000000000 gm87_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25044250885923669036169974251216000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 0 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25044250885923669036169974251216000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25044250885923669036169974251216000000000000000000000000 gm87_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 0 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 0 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 0 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg87 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 (87 : Fin 88)),
            if yzBoundary 1 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr ((87 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr ((87 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((75986709850504446043722278009668681388910051034004000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp87 (fun b ↦
    if yzBoundary 1 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
      ((∑ w, mu3 0 2 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 0 2 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(87 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(87 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(87 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(87 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) from Or.inr rfl)]
  rw [hJ87]
  rw [kzero _ gm87_2]
  rw [kzero _ gm87_3]
  rw [kzero _ gm87_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb87_3_0_1 (add_le_add cb87_4_0_0 (add_le_add gb87_0 gb87_1))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((200369674577777681966095809922344830587752009668590607078151012417000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg66 (add_le_add L3K.reg67 (add_le_add L3K.reg68 (add_le_add L3K.reg69 (add_le_add L3K.reg70 (add_le_add L3K.reg71 (add_le_add L3K.reg72 (add_le_add L3K.reg73 (add_le_add L3K.reg74 (add_le_add L3K.reg75 (add_le_add L3K.reg76 (add_le_add L3K.reg77 (add_le_add L3K.reg78 (add_le_add L3K.reg79 (add_le_add L3K.reg80 (add_le_add L3K.reg81 (add_le_add L3K.reg82 (add_le_add L3K.reg83 (add_le_add L3K.reg84 (add_le_add L3K.reg85 (add_le_add L3K.reg86 L3K.reg87))))))))))))))))))))) (le_of_eq (by push_cast; ring))
