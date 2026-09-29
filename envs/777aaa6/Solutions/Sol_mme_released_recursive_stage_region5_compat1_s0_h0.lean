-- Prove2me | solution 1 for mme_released_recursive_stage_region5_compat1_s0_h0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T14:17:54.010366+00:00
-- url     : https://prove2.me/submissions/a247f00e-3dcc-4783-be09-8c99bf9f57a4

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat61
import Theorems.Thm_mme_released_recursive_level3_compat62
import Theorems.Thm_mme_released_recursive_level3_compat63
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



noncomputable abbrev MU := partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)

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
    (hb : yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 5 1 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 5 1 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp0 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ0 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm0_3_1_0 :
    ∑ w, mu3 5 1 (⟨(0 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84616717252006186217231178351936000000000000000000000000 := by
  decide +kernel

theorem cb0_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(0 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(0 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84616717252006186217231178351936000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (0 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.1 84616717252006186217231178351936000000000000000000000000 cm0_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm0_4_0_0 :
    ∑ w, mu3 5 1 (⟨(0 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25048399691437587174768821648064000000000000000000000000 := by
  decide +kernel

theorem cb0_4_0_0 :
    ((∑ w, mu3 5 1 (⟨(0 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(0 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25048399691437587174768821648064000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (0 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.1 25048399691437587174768821648064000000000000000000000000 cm0_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84616717252006186217231178351936000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb0_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84616717252006186217231178351936000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.1 84616717252006186217231178351936000000000000000000000000 gm0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25048399691437587174768821648064000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb0_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25048399691437587174768821648064000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.1 25048399691437587174768821648064000000000000000000000000 gm0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm0_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm0_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg0 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (0 : Fin 88)),
            if yzBoundary 0 (⟨(0 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(0 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(0 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((0 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((0 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76014066615124738854397499515198940551929105054096000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp0 (fun b ↦
    if yzBoundary 0 (⟨(0 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(0 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(0 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(0 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(0 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(0 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(0 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ0]
  rw [kzero _ gm0_2]
  rw [kzero _ gm0_3]
  rw [kzero _ gm0_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb0_3_1_0 (add_le_add cb0_4_0_0 (add_le_add gb0_0 gb0_1))) (le_of_eq (by push_cast; ring)))

theorem hsp1 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ1 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm1_0_4_0 :
    ∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 21568558504572835666775934640989000000000000000000000000 := by
  decide +kernel

theorem cb1_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((21568558504572835666775934640989000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.1 21568558504572835666775934640989000000000000000000000000 cm1_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm1_1_3_0 :
    ∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 4169301267862191107002137513352962000000000000000000000000 := by
  decide +kernel

theorem cb1_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((4169301267862191107002137513352962000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.1 4169301267862191107002137513352962000000000000000000000000 cm1_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm1_2_2_0 :
    ∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 28279927914606740342877619946395767000000000000000000000000 := by
  decide +kernel

theorem cb1_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((28279927914606740342877619946395767000000000000000000000000 * 377275938144459829825412027496 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((377275938144459829825412027496 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28279927914606740342877619946395767000000000000000000000000 cm1_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm1_3_1_0 :
    ∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 814761585137418543902466605610282000000000000000000000000 := by
  decide +kernel

theorem cb1_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(1 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(1 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((814761585137418543902466605610282000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 814761585137418543902466605610282000000000000000000000000 cm1_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21568558504572835666775934640989000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21568558504572835666775934640989000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21568558504572835666775934640989000000000000000000000000 gm1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4169301267862191107002137513352962000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4169301267862191107002137513352962000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.1 4169301267862191107002137513352962000000000000000000000000 gm1_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 28279927914606740342877619946395767000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((28279927914606740342877619946395767000000000000000000000000 * 18639080405229388845651055767 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((18639080405229388845651055767 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.1 28279927914606740342877619946395767000000000000000000000000 gm1_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 814761585137418543902466605610282000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((814761585137418543902466605610282000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.1 814761585137418543902466605610282000000000000000000000000 gm1_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg1 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (1 : Fin 88)),
            if yzBoundary 0 (⟨(1 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(1 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(1 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((1 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((1 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((18105826413475874719232113156924389404919556082537422667288280495000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp1 (fun b ↦
    if yzBoundary 0 (⟨(1 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(1 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(1 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ1]
  rw [kzero _ gm1_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb1_0_4_0 (add_le_add cb1_1_3_0 (add_le_add cb1_2_2_0 (add_le_add cb1_3_1_0 (add_le_add gb1_0 (add_le_add gb1_1 (add_le_add gb1_2 gb1_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp2 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ2 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm2_0_4_0 :
    ∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 29063459527714256112975025808620000000000000000000000000 := by
  decide +kernel

theorem cb2_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((29063459527714256112975025808620000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29063459527714256112975025808620000000000000000000000000 cm2_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm2_1_3_0 :
    ∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1311911883639468456814743080330860000000000000000000000000 := by
  decide +kernel

theorem cb2_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1311911883639468456814743080330860000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1311911883639468456814743080330860000000000000000000000000 cm2_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm2_2_2_0 :
    ∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 723109203184358184052281893860520000000000000000000000000 := by
  decide +kernel

theorem cb2_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((723109203184358184052281893860520000000000000000000000000 * 412604678011392911814364993193 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((412604678011392911814364993193 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 723109203184358184052281893860520000000000000000000000000 cm2_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm2_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29063459527714256112975025808620000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29063459527714256112975025808620000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29063459527714256112975025808620000000000000000000000000 gm2_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1311911883639468456814743080330860000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1311911883639468456814743080330860000000000000000000000000 * 173800976950076151029811231 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((173800976950076151029811231 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1311911883639468456814743080330860000000000000000000000000 gm2_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 723109203184358184052281893860520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((723109203184358184052281893860520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 723109203184358184052281893860520000000000000000000000000 gm2_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg2 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (2 : Fin 88)),
            if yzBoundary 0 (⟨(2 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(2 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(2 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((2 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((2 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1729300635254930278160905802789590518352111626703723598295989360000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp2 (fun b ↦
    if yzBoundary 0 (⟨(2 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(2 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(2 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ2]
  rw [kzero _ gm2_0]
  rw [kzero _ gm2_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb2_0_4_0 (add_le_add cb2_1_3_0 (add_le_add cb2_2_2_0 (add_le_add gb2_1 (add_le_add gb2_2 gb2_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp3 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ3 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm3_0_4_0 :
    ∑ w, mu3 5 1 (⟨(3 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25835617705221565331134667832118000000000000000000000000 := by
  decide +kernel

theorem cb3_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(3 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(3 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25835617705221565331134667832118000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (3 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25835617705221565331134667832118000000000000000000000000 cm3_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm3_1_3_0 :
    ∑ w, mu3 5 1 (⟨(3 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84379634930828349502865332167882000000000000000000000000 := by
  decide +kernel

theorem cb3_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(3 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(3 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84379634930828349502865332167882000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (3 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84379634930828349502865332167882000000000000000000000000 cm3_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm3_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm3_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25835617705221565331134667832118000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb3_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25835617705221565331134667832118000000000000000000000000 * 179130449806506801136297212994 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -1 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((179130449806506801136297212994 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25835617705221565331134667832118000000000000000000000000 gm3_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84379634930828349502865332167882000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb3_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84379634930828349502865332167882000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84379634930828349502865332167882000000000000000000000000 gm3_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg3 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (3 : Fin 88)),
            if yzBoundary 0 (⟨(3 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(3 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(3 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((3 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((3 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((121602957918527582656710212912786475607510007350961774952980702000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp3 (fun b ↦
    if yzBoundary 0 (⟨(3 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(3 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(3 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(3 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(3 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(3 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(3 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ3]
  rw [kzero _ gm3_0]
  rw [kzero _ gm3_1]
  rw [kzero _ gm3_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb3_0_4_0 (add_le_add cb3_1_3_0 (add_le_add gb3_2 gb3_3))) (le_of_eq (by push_cast; ring)))

theorem hsp4 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ4 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm4_1_3_0 :
    ∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 708473934990572013808917315377256000000000000000000000000 := by
  decide +kernel

theorem cb4_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((708473934990572013808917315377256000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 708473934990572013808917315377256000000000000000000000000 cm4_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm4_2_2_0 :
    ∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 10035498964441306647727577653520103000000000000000000000000 := by
  decide +kernel

theorem cb4_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((10035498964441306647727577653520103000000000000000000000000 * 403044207312311673592271932084 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403044207312311673592271932084 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10035498964441306647727577653520103000000000000000000000000 cm4_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm4_3_1_0 :
    ∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 658962994416293861113011431600226000000000000000000000000 := by
  decide +kernel

theorem cb4_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(4 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(4 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((658962994416293861113011431600226000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 658962994416293861113011431600226000000000000000000000000 cm4_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 800895135909909275324391104286135000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((800895135909909275324391104286135000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 800895135909909275324391104286135000000000000000000000000 gm4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29241468938797524709415597464113639000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29241468938797524709415597464113639000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29241468938797524709415597464113639000000000000000000000000 gm4_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 19864932968772511922801031242193762000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((19864932968772511922801031242193762000000000000000000000000 * 96928218950918054655292074473 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((96928218950918054655292074473 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19864932968772511922801031242193762000000000000000000000000 gm4_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 92421200919337261515473788908879000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((92421200919337261515473788908879000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 92421200919337261515473788908879000000000000000000000000 gm4_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg4 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (4 : Fin 88)),
            if yzBoundary 0 (⟨(4 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(4 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(4 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((4 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((4 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27250760594761104868059795295151915507228245416504184653674725023000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp4 (fun b ↦
    if yzBoundary 0 (⟨(4 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(4 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(4 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ4]
  rw [kzero _ gm4_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb4_1_3_0 (add_le_add cb4_2_2_0 (add_le_add cb4_3_1_0 (add_le_add gb4_0 (add_le_add gb4_1 (add_le_add gb4_2 gb4_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp5 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ5 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm5_0_4_0 :
    ∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5125112500754521588792867893120000000000000000000000000 := by
  decide +kernel

theorem cb5_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(5 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5125112500754521588792867893120000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5125112500754521588792867893120000000000000000000000000 cm5_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm5_1_3_0 :
    ∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 628832006077821452327742343078320000000000000000000000000 := by
  decide +kernel

theorem cb5_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((628832006077821452327742343078320000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 628832006077821452327742343078320000000000000000000000000 cm5_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm5_2_2_0 :
    ∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 2251052708144510678633050921875120000000000000000000000000 := by
  decide +kernel

theorem cb5_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((2251052708144510678633050921875120000000000000000000000000 * 374829119699071979972876887572 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((374829119699071979972876887572 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2251052708144510678633050921875120000000000000000000000000 cm5_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5125112500754521588792867893120000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5125112500754521588792867893120000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5125112500754521588792867893120000000000000000000000000 gm5_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1187998099960133958010965618017520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1187998099960133958010965618017520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1187998099960133958010965618017520000000000000000000000000 gm5_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10956479956313641702487432106303600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10956479956313641702487432106303600000000000000000000000000 * 202543187273603174825684084677 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 1 else if k.val = 2 then -5 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((202543187273603174825684084677 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10956479956313641702487432106303600000000000000000000000000 gm5_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 559166093882312505683223274939200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((559166093882312505683223274939200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 559166093882312505683223274939200000000000000000000000000 gm5_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg5 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (5 : Fin 88)),
            if yzBoundary 0 (⟨(5 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(5 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(5 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((5 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((5 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4709835543637010257196906081961237039927679347873144735420659760000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp5 (fun b ↦
    if yzBoundary 0 (⟨(5 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(5 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(5 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ5]
  rw [kzero _ gm5_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb5_0_4_0 (add_le_add cb5_1_3_0 (add_le_add cb5_2_2_0 (add_le_add gb5_0 (add_le_add gb5_1 (add_le_add gb5_2 gb5_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp6 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ6 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm6_0_4_0 :
    ∑ w, mu3 5 1 (⟨(6 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 8548932433992699921039171453555000000000000000000000000 := by
  decide +kernel

theorem cb6_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(6 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(6 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((8548932433992699921039171453555000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (6 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8548932433992699921039171453555000000000000000000000000 cm6_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm6_1_3_0 :
    ∑ w, mu3 5 1 (⟨(6 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 210123624778729852153055687935989000000000000000000000000 := by
  decide +kernel

theorem cb6_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(6 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(6 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((210123624778729852153055687935989000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (6 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 210123624778729852153055687935989000000000000000000000000 cm6_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm6_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8548932433992699921039171453555000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8548932433992699921039171453555000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8548932433992699921039171453555000000000000000000000000 gm6_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 588857959236895106837960828546445000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((588857959236895106837960828546445000000000000000000000000 * 227873354318166024763513160113 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-37 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((227873354318166024763513160113 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 588857959236895106837960828546445000000000000000000000000 gm6_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 378734334458165254684905140610456000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((378734334458165254684905140610456000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 378734334458165254684905140610456000000000000000000000000 gm6_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg6 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (6 : Fin 88)),
            if yzBoundary 0 (⟨(6 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(6 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(6 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((6 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((6 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((548275940997017722738140718600004856702597454957085276542123170000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp6 (fun b ↦
    if yzBoundary 0 (⟨(6 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(6 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(6 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(6 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(6 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ6]
  rw [kzero _ gm6_0]
  rw [kzero _ gm6_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb6_0_4_0 (add_le_add cb6_1_3_0 (add_le_add gb6_1 (add_le_add gb6_2 gb6_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp7 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ7 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm7_2_2_0 :
    ∑ w, mu3 5 1 (⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 563247814457902738378476384251907000000000000000000000000 := by
  decide +kernel

theorem cb7_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((563247814457902738378476384251907000000000000000000000000 * 398413812501997993343088635081 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (7 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398413812501997993343088635081 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.1 563247814457902738378476384251907000000000000000000000000 cm7_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm7_3_1_0 :
    ∑ w, mu3 5 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 76223669727210678773855284576359000000000000000000000000 := by
  decide +kernel

theorem cb7_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((76223669727210678773855284576359000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.1 76223669727210678773855284576359000000000000000000000000 cm7_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8575273335280899281005330006297128000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb7_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8575273335280899281005330006297128000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.1 8575273335280899281005330006297128000000000000000000000000 gm7_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29213807372199072202257484702829385000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb7_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29213807372199072202257484702829385000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29213807372199072202257484702829385000000000000000000000000 gm7_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8012025520822996542626853622045221000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb7_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8012025520822996542626853622045221000000000000000000000000 * 207730739489954336058354222394 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -5 else if k.val = 2 then -5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207730739489954336058354222394 : ℚ)/10^30) mme_released_recursive_level3_compat61.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 8012025520822996542626853622045221000000000000000000000000 gm7_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm7_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg7 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (7 : Fin 88)),
            if yzBoundary 0 (⟨(7 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(7 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(7 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((7 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((7 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((22191052130619018862148017973209348236174341054202979239580742901000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp7 (fun b ↦
    if yzBoundary 0 (⟨(7 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(7 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(7 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(7 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ7]
  rw [kzero _ gm7_3]
  rw [kzero _ gm7_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb7_2_2_0 (add_le_add cb7_3_1_0 (add_le_add gb7_0 (add_le_add gb7_1 gb7_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp8 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ8 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm8_3_1_0 :
    ∑ w, mu3 5 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 3953963419649615893412844552200000000000000000000000000 := by
  decide +kernel

theorem cb8_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((3953963419649615893412844552200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3953963419649615893412844552200000000000000000000000000 cm8_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6036149056696759585700000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb8_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6036149056696759585700000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.1 6036149056696759585700000000000000000000000000000000000000 gm8_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6032195093277109969806587155447800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb8_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6032195093277109969806587155447800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.1 6032195093277109969806587155447800000000000000000000000000 gm8_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm8_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm8_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg8 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (8 : Fin 88)),
            if yzBoundary 0 (⟨(8 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(8 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(8 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((8 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((8 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4183939700088932373206529470964727511257425974614100000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp8 (fun b ↦
    if yzBoundary 0 (⟨(8 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(8 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(8 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ8]
  rw [kzero _ gm8_2]
  rw [kzero _ gm8_3]
  rw [kzero _ gm8_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb8_3_1_0 (add_le_add gb8_0 gb8_1)) (le_of_eq (by push_cast; ring)))

theorem hsp9 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ9 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm9_1_3_0 :
    ∑ w, mu3 5 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 7013866001599648674077495262648000000000000000000000000 := by
  decide +kernel

theorem cb9_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((7013866001599648674077495262648000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7013866001599648674077495262648000000000000000000000000 cm9_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 278311107235807202167948401196990000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((278311107235807202167948401196990000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 278311107235807202167948401196990000000000000000000000000 gm9_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10346332696214259408195051598803010000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10346332696214259408195051598803010000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10346332696214259408195051598803010000000000000000000000000 gm9_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10346332696214259408195051598803010000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10346332696214259408195051598803010000000000000000000000000 * 361620723030697814492455735044 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361620723030697814492455735044 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10346332696214259408195051598803010000000000000000000000000 gm9_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 271297241234207553493870905934342000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((271297241234207553493870905934342000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 271297241234207553493870905934342000000000000000000000000 gm9_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg9 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (9 : Fin 88)),
            if yzBoundary 0 (⟨(9 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(9 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(9 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((9 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((9 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((11105890207136257055642668445226805973233410625109537318918061370000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp9 (fun b ↦
    if yzBoundary 0 (⟨(9 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(9 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(9 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ9]
  rw [kzero _ gm9_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb9_1_3_0 (add_le_add gb9_0 (add_le_add gb9_1 (add_le_add gb9_2 gb9_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp10 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ10 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm10_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2822221029727433653130000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb10_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2822221029727433653130000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2822221029727433653130000000000000000000000000000000000000 gm10_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm10_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2822221029727433653130000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb10_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2822221029727433653130000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2822221029727433653130000000000000000000000000000000000000 gm10_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm10_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm10_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm10_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg10 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (10 : Fin 88)),
            if yzBoundary 0 (⟨(10 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(10 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(10 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((10 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((10 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1956214549672556233038707443011831865952845927490690000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp10 (fun b ↦
    if yzBoundary 0 (⟨(10 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(10 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(10 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ10]
  rw [kzero _ gm10_2]
  rw [kzero _ gm10_3]
  rw [kzero _ gm10_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb10_0 gb10_1) (le_of_eq (by push_cast; ring)))

theorem hsp11 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ11 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm11_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1180386674298232045379105723485056000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1180386674298232045379105723485056000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1180386674298232045379105723485056000000000000000000000000 gm11_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4032770927080953386233788553029888000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4032770927080953386233788553029888000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4032770927080953386233788553029888000000000000000000000000 gm11_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1180386674298232045379105723485056000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1180386674298232045379105723485056000000000000000000000000 * 424640235469174621957933225569 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424640235469174621957933225569 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1180386674298232045379105723485056000000000000000000000000 gm11_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm11_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg11 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (11 : Fin 88)),
            if yzBoundary 0 (⟨(11 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(11 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(11 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((11 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((11 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3296543473268956823464936574069955137631118241475252821335171584000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp11 (fun b ↦
    if yzBoundary 0 (⟨(11 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(11 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(11 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ11]
  rw [kzero _ gm11_3]
  rw [kzero _ gm11_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb11_0 (add_le_add gb11_1 gb11_2)) (le_of_eq (by push_cast; ring)))

theorem hsp12 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ12 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm12_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111396472849910118576000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb12_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111396472849910118576000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111396472849910118576000000000000000000000000000000000000 gm12_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm12_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111396472849910118576000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb12_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111396472849910118576000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111396472849910118576000000000000000000000000000000000000 gm12_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm12_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm12_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm12_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg12 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (12 : Fin 88)),
            if yzBoundary 0 (⟨(12 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(12 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(12 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((12 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((12 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((77214151080237694402351332206299662634869039541488000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp12 (fun b ↦
    if yzBoundary 0 (⟨(12 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(12 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(12 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ12]
  rw [kzero _ gm12_2]
  rw [kzero _ gm12_3]
  rw [kzero _ gm12_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb12_0 gb12_1) (le_of_eq (by push_cast; ring)))

theorem hsp13 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ13 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm13_3_1_0 :
    ∑ w, mu3 5 1 (⟨(13 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84573771860662974465177634588200000000000000000000000000 := by
  decide +kernel

theorem cb13_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(13 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(13 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84573771860662974465177634588200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (13 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84573771860662974465177634588200000000000000000000000000 cm13_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm13_4_0_0 :
    ∑ w, mu3 5 1 (⟨(13 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25762044474474291734822365411800000000000000000000000000 := by
  decide +kernel

theorem cb13_4_0_0 :
    ((∑ w, mu3 5 1 (⟨(13 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(13 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25762044474474291734822365411800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (13 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25762044474474291734822365411800000000000000000000000000 cm13_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm13_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84573771860662974465177634588200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb13_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84573771860662974465177634588200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84573771860662974465177634588200000000000000000000000000 gm13_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm13_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25762044474474291734822365411800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb13_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25762044474474291734822365411800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25762044474474291734822365411800000000000000000000000000 gm13_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm13_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm13_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm13_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg13 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (13 : Fin 88)),
            if yzBoundary 0 (⟨(13 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(13 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(13 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((13 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((13 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76478960007480353797020743738166948400781384460600000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp13 (fun b ↦
    if yzBoundary 0 (⟨(13 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(13 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(13 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(13 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(13 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ13]
  rw [kzero _ gm13_2]
  rw [kzero _ gm13_3]
  rw [kzero _ gm13_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb13_3_1_0 (add_le_add cb13_4_0_0 (add_le_add gb13_0 gb13_1))) (le_of_eq (by push_cast; ring)))

theorem hsp14 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ14 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm14_0_4_0 :
    ∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25199329944093208489587777821136000000000000000000000000 := by
  decide +kernel

theorem cb14_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25199329944093208489587777821136000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25199329944093208489587777821136000000000000000000000000 cm14_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm14_1_3_0 :
    ∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 4526603701696796234496714889369200000000000000000000000000 := by
  decide +kernel

theorem cb14_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((4526603701696796234496714889369200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4526603701696796234496714889369200000000000000000000000000 cm14_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm14_2_2_0 :
    ∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 33197045152693449035617173486733104000000000000000000000000 := by
  decide +kernel

theorem cb14_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(14 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((33197045152693449035617173486733104000000000000000000000000 * 368652170896525720440036052878 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((368652170896525720440036052878 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33197045152693449035617173486733104000000000000000000000000 cm14_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm14_3_1_0 :
    ∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 936845203938308438852523846076560000000000000000000000000 := by
  decide +kernel

theorem cb14_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(14 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(14 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((936845203938308438852523846076560000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 936845203938308438852523846076560000000000000000000000000 cm14_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25199329944093208489587777821136000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25199329944093208489587777821136000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25199329944093208489587777821136000000000000000000000000 gm14_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4526603701696796234496714889369200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4526603701696796234496714889369200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4526603701696796234496714889369200000000000000000000000000 gm14_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33197045152693449035617173486733104000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33197045152693449035617173486733104000000000000000000000000 * 10588673341427586148592747831 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -3 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10588673341427586148592747831 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33197045152693449035617173486733104000000000000000000000000 gm14_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 936845203938308438852523846076560000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((936845203938308438852523846076560000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 936845203938308438852523846076560000000000000000000000000 gm14_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg14 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (14 : Fin 88)),
            if yzBoundary 0 (⟨(14 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(14 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(14 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((14 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((14 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((20163623840061502151169736190812543737218989775073129587763815760000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp14 (fun b ↦
    if yzBoundary 0 (⟨(14 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(14 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(14 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ14]
  rw [kzero _ gm14_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb14_0_4_0 (add_le_add cb14_1_3_0 (add_le_add cb14_2_2_0 (add_le_add cb14_3_1_0 (add_le_add gb14_0 (add_le_add gb14_1 (add_le_add gb14_2 gb14_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp15 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ15 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm15_0_4_0 :
    ∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 31106365386967989250166827420306000000000000000000000000 := by
  decide +kernel

theorem cb15_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((31106365386967989250166827420306000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.1 31106365386967989250166827420306000000000000000000000000 cm15_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm15_1_3_0 :
    ∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1505267448122598856113479579783958000000000000000000000000 := by
  decide +kernel

theorem cb15_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1505267448122598856113479579783958000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.1 1505267448122598856113479579783958000000000000000000000000 cm15_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm15_2_2_0 :
    ∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 807703612335937585298353592795736000000000000000000000000 := by
  decide +kernel

theorem cb15_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((807703612335937585298353592795736000000000000000000000000 * 378229754076570791202447657690 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378229754076570791202447657690 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.1 807703612335937585298353592795736000000000000000000000000 cm15_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm15_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 31106365386967989250166827420306000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((31106365386967989250166827420306000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.1 31106365386967989250166827420306000000000000000000000000 gm15_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1505267448122598856113479579783958000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1505267448122598856113479579783958000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.1 1505267448122598856113479579783958000000000000000000000000 gm15_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 807703612335937585298353592795736000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((807703612335937585298353592795736000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat62.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 807703612335937585298353592795736000000000000000000000000 gm15_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg15 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (15 : Fin 88)),
            if yzBoundary 0 (⟨(15 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(15 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(15 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((15 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((15 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1930288197399605214204270953556753754606729912123586336670039688000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp15 (fun b ↦
    if yzBoundary 0 (⟨(15 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(15 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(15 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ15]
  rw [kzero _ gm15_0]
  rw [kzero _ gm15_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb15_0_4_0 (add_le_add cb15_1_3_0 (add_le_add cb15_2_2_0 (add_le_add gb15_1 (add_le_add gb15_2 gb15_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp16 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ16 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm16_0_4_0 :
    ∑ w, mu3 5 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 25127754864913942284278182164864000000000000000000000000 := by
  decide +kernel

theorem cb16_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((25127754864913942284278182164864000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.1 25127754864913942284278182164864000000000000000000000000 cm16_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm16_1_3_0 :
    ∑ w, mu3 5 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 84458627961770793619721817835136000000000000000000000000 := by
  decide +kernel

theorem cb16_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((84458627961770793619721817835136000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.1 84458627961770793619721817835136000000000000000000000000 cm16_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm16_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm16_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25127754864913942284278182164864000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25127754864913942284278182164864000000000000000000000000 * 32569704485555790493858935 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((32569704485555790493858935 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.1 25127754864913942284278182164864000000000000000000000000 gm16_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84458627961770793619721817835136000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84458627961770793619721817835136000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.1 84458627961770793619721817835136000000000000000000000000 gm16_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg16 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (16 : Fin 88)),
            if yzBoundary 0 (⟨(16 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(16 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(16 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((16 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((16 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117085338094875907675724209939904747350108556255139442194635520000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp16 (fun b ↦
    if yzBoundary 0 (⟨(16 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(16 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(16 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ16]
  rw [kzero _ gm16_0]
  rw [kzero _ gm16_1]
  rw [kzero _ gm16_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb16_0_4_0 (add_le_add cb16_1_3_0 (add_le_add gb16_2 gb16_3))) (le_of_eq (by push_cast; ring)))

theorem hsp17 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ17 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm17_3_1_0 :
    ∑ w, mu3 5 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 141286618861470487311052991759224000000000000000000000000 := by
  decide +kernel

theorem cb17_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((141286618861470487311052991759224000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 141286618861470487311052991759224000000000000000000000000 cm17_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm17_4_0_0 :
    ∑ w, mu3 5 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5746087973194682637989852483232000000000000000000000000 := by
  decide +kernel

theorem cb17_4_0_0 :
    ((∑ w, mu3 5 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5746087973194682637989852483232000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5746087973194682637989852483232000000000000000000000000 cm17_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 396056708849556392458010147516768000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb17_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((396056708849556392458010147516768000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 396056708849556392458010147516768000000000000000000000000 gm17_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 260516177961280587784947008240776000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb17_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((260516177961280587784947008240776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 260516177961280587784947008240776000000000000000000000000 gm17_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm17_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm17_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg17 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (17 : Fin 88)),
            if yzBoundary 0 (⟨(17 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(17 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(17 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((17 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((17 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((278508475758790458936385584586682260338225131976248000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp17 (fun b ↦
    if yzBoundary 0 (⟨(17 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(17 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(17 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ17]
  rw [kzero _ gm17_2]
  rw [kzero _ gm17_3]
  rw [kzero _ gm17_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb17_3_1_0 (add_le_add cb17_4_0_0 (add_le_add gb17_0 gb17_1))) (le_of_eq (by push_cast; ring)))

theorem hsp18 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ18 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm18_2_2_0 :
    ∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 5214071316379349437204039521587880000000000000000000000000 := by
  decide +kernel

theorem cb18_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(18 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((5214071316379349437204039521587880000000000000000000000000 * 333754403704687814973558720886 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (18 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((333754403704687814973558720886 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5214071316379349437204039521587880000000000000000000000000 cm18_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm18_3_1_0 :
    ∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 1435797165660361321619089516941300000000000000000000000000 := by
  decide +kernel

theorem cb18_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(18 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((1435797165660361321619089516941300000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (18 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1435797165660361321619089516941300000000000000000000000000 cm18_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm18_4_0_0 :
    ∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 11878713990606976789085635064820000000000000000000000000 := by
  decide +kernel

theorem cb18_4_0_0 :
    ((∑ w, mu3 5 1 (⟨(18 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(18 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((11878713990606976789085635064820000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (18 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11878713990606976789085635064820000000000000000000000000 cm18_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6553102727171862273311362462566840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6553102727171862273311362462566840000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6553102727171862273311362462566840000000000000000000000000 gm18_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21564071558649550675740014287795380000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21564071558649550675740014287795380000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21564071558649550675740014287795380000000000000000000000000 gm18_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1350910124783119812896408576043780000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1350910124783119812896408576043780000000000000000000000000 * 5578481481351459429233941 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -5 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5578481481351459429233941 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1350910124783119812896408576043780000000000000000000000000 gm18_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm18_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg18 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (18 : Fin 88)),
            if yzBoundary 0 (⟨(18 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(18 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(18 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((18 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((18 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17682520958603302045228293962510094236852482997683001292270240360000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp18 (fun b ↦
    if yzBoundary 0 (⟨(18 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(18 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(18 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(18 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(18 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(18 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ18]
  rw [kzero _ gm18_3]
  rw [kzero _ gm18_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb18_2_2_0 (add_le_add cb18_3_1_0 (add_le_add cb18_4_0_0 (add_le_add gb18_0 (add_le_add gb18_1 gb18_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp19 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ19 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm19_1_3_0 :
    ∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 806149687384070090669278554426540000000000000000000000000 := by
  decide +kernel

theorem cb19_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((806149687384070090669278554426540000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 806149687384070090669278554426540000000000000000000000000 cm19_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm19_2_2_0 :
    ∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 11505190799990736456040811649001700000000000000000000000000 := by
  decide +kernel

theorem cb19_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((11505190799990736456040811649001700000000000000000000000000 * 403510190282139785216657667716 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403510190282139785216657667716 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11505190799990736456040811649001700000000000000000000000000 cm19_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm19_3_1_0 :
    ∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 759253946343585870693785348524330000000000000000000000000 := by
  decide +kernel

theorem cb19_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(19 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(19 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((759253946343585870693785348524330000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 759253946343585870693785348524330000000000000000000000000 cm19_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 911868079959310417615419460186050000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((911868079959310417615419460186050000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 911868079959310417615419460186050000000000000000000000000 gm19_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33516158759480228057120795191289620000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33516158759480228057120795191289620000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33516158759480228057120795191289620000000000000000000000000 gm19_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22770221905833077471773768890812250000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22770221905833077471773768890812250000000000000000000000000 * 95738736918337141905559488703 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((95738736918337141905559488703 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22770221905833077471773768890812250000000000000000000000000 gm19_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 105718392575240326946140905759510000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((105718392575240326946140905759510000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 105718392575240326946140905759510000000000000000000000000 gm19_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg19 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (19 : Fin 88)),
            if yzBoundary 0 (⟨(19 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(19 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(19 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((19 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((19 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31212418481788006055269352634517629990233766726843218822309431300000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp19 (fun b ↦
    if yzBoundary 0 (⟨(19 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(19 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(19 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ19]
  rw [kzero _ gm19_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb19_1_3_0 (add_le_add cb19_2_2_0 (add_le_add cb19_3_1_0 (add_le_add gb19_0 (add_le_add gb19_1 (add_le_add gb19_2 gb19_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp20 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ20 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm20_0_4_0 :
    ∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 554551834224713131067489623252000000000000000000000000 := by
  decide +kernel

theorem cb20_0_4_0 :
    ((∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((554551834224713131067489623252000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 554551834224713131067489623252000000000000000000000000 cm20_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm20_1_3_0 :
    ∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 65650813159783042653130981249080000000000000000000000000 := by
  decide +kernel

theorem cb20_1_3_0 :
    ((∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((65650813159783042653130981249080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 65650813159783042653130981249080000000000000000000000000 cm20_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm20_2_2_0 :
    ∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 254155781868687015280454000547180000000000000000000000000 := by
  decide +kernel

theorem cb20_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((254155781868687015280454000547180000000000000000000000000 * 370428099831337312976676709029 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370428099831337312976676709029 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 254155781868687015280454000547180000000000000000000000000 cm20_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 554551834224713131067489623252000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((554551834224713131067489623252000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 554551834224713131067489623252000000000000000000000000 gm20_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 124804603385641957875649784617528000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((124804603385641957875649784617528000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 124804603385641957875649784617528000000000000000000000000 gm20_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1234146499597299967050111450971260000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1234146499597299967050111450971260000000000000000000000000 * 188362717444457333362729699617 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((188362717444457333362729699617 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1234146499597299967050111450971260000000000000000000000000 gm20_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 59153790225858915222518803368448000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((59153790225858915222518803368448000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 59153790225858915222518803368448000000000000000000000000 gm20_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg20 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (20 : Fin 88)),
            if yzBoundary 0 (⟨(20 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(20 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(20 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((20 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((20 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((499629549642797729021363275097427636927834150751651152664631504000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp20 (fun b ↦
    if yzBoundary 0 (⟨(20 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(20 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(20 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ20]
  rw [kzero _ gm20_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb20_0_4_0 (add_le_add cb20_1_3_0 (add_le_add cb20_2_2_0 (add_le_add gb20_0 (add_le_add gb20_1 (add_le_add gb20_2 gb20_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp21 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ21 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm21_2_2_0 :
    ∑ w, mu3 5 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 625111799980634657306472806971632000000000000000000000000 := by
  decide +kernel

theorem cb21_2_2_0 :
    ((∑ w, mu3 5 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((625111799980634657306472806971632000000000000000000000000 * 398985575146383506444930358860 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398985575146383506444930358860 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 625111799980634657306472806971632000000000000000000000000 cm21_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm21_3_1_0 :
    ∑ w, mu3 5 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w = 85042871745728231596917600698000000000000000000000000000 := by
  decide +kernel

theorem cb21_3_1_0 :
    ((∑ w, mu3 5 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5))) w : ℚ) : ℝ)) ≤
      ((85042871745728231596917600698000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85042871745728231596917600698000000000000000000000000000 cm21_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9522469039401869850224678031756776000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 5 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9522469039401869850224678031756776000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9522469039401869850224678031756776000000000000000000000000 gm21_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32422053571736710363329726335788448000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 5 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32422053571736710363329726335788448000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32422053571736710363329726335788448000000000000000000000000 gm21_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8897357239421235192918205224785144000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 5 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8897357239421235192918205224785144000000000000000000000000 * 207639152831399594615332784140 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207639152831399594615332784140 : ℚ)/10^30) mme_released_recursive_level3_compat63.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8897357239421235192918205224785144000000000000000000000000 gm21_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 5 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm21_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 5 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg21 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 (21 : Fin 88)),
            if yzBoundary 0 (⟨(21 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨(21 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(21 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr ((21 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr ((21 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((24629052558667887880962496166289006497240792142544599694655891800000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp21 (fun b ↦
    if yzBoundary 0 (⟨(21 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
      ((∑ w, mu3 5 1 ⟨(21 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 5 1 ⟨(21 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) from rfl)]
  rw [hJ21]
  rw [kzero _ gm21_3]
  rw [kzero _ gm21_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb21_2_2_0 (add_le_add cb21_3_1_0 (add_le_add gb21_0 (add_le_add gb21_1 gb21_2)))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 5 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 5)) then
              ((∑ w, mu3 5 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 5 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 5 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((191942076724549797005066823727592300939343350681125840414537420297000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg0 (add_le_add L3K.reg1 (add_le_add L3K.reg2 (add_le_add L3K.reg3 (add_le_add L3K.reg4 (add_le_add L3K.reg5 (add_le_add L3K.reg6 (add_le_add L3K.reg7 (add_le_add L3K.reg8 (add_le_add L3K.reg9 (add_le_add L3K.reg10 (add_le_add L3K.reg11 (add_le_add L3K.reg12 (add_le_add L3K.reg13 (add_le_add L3K.reg14 (add_le_add L3K.reg15 (add_le_add L3K.reg16 (add_le_add L3K.reg17 (add_le_add L3K.reg18 (add_le_add L3K.reg19 (add_le_add L3K.reg20 L3K.reg21))))))))))))))))))))) (le_of_eq (by push_cast; ring))
