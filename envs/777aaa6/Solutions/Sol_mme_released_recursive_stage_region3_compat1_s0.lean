-- Prove2me | solution 1 for mme_released_recursive_stage_region3_compat1_s0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T09:32:28.568119+00:00
-- url     : https://prove2.me/submissions/b61139c8-22bc-4782-8332-1c5aca157d3d

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat37
import Theorems.Thm_mme_released_recursive_level3_compat38
import Theorems.Thm_mme_released_recursive_level3_compat39
import Theorems.Thm_mme_released_recursive_level3_compat40
import Theorems.Thm_mme_released_recursive_level3_compat41
import Theorems.Thm_mme_released_recursive_level3_compat42
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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 3 1 ⟨rr, c⟩ w else 0 := by
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



noncomputable abbrev MU := partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)

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

theorem kstepC (a : Fin 88) (b : Split (2 * 2 ^ (2 - 1)) (parent3 3 a))
    (hb : yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 3 1 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 3 1 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp0 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
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

theorem cm0_0_4_0 :
    ∑ w, mu3 3 1 (⟨(0 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25056396834145960628998511757675000000000000000000000000 := by
  decide +kernel

theorem cb0_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(0 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(0 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25056396834145960628998511757675000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (0 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.1 25056396834145960628998511757675000000000000000000000000 cm0_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm0_1_3_0 :
    ∑ w, mu3 3 1 (⟨(0 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84581522334304233366001488242325000000000000000000000000 := by
  decide +kernel

theorem cb0_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(0 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(0 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84581522334304233366001488242325000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (0 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.1 84581522334304233366001488242325000000000000000000000000 cm0_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm0_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm0_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25056396834145960628998511757675000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb0_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25056396834145960628998511757675000000000000000000000000 * 102343935778881254314362122 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((0 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((102343935778881254314362122 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.1 25056396834145960628998511757675000000000000000000000000 gm0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84581522334304233366001488242325000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb0_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84581522334304233366001488242325000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((0 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.1 84581522334304233366001488242325000000000000000000000000 gm0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm0_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(0 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (0 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg0 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (0 : Fin 88)),
            if yzBoundary 0 (⟨(0 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(0 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(0 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((0 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((0 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117257451837250490626106758824331606511255685494280415553997975000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp0 (fun b ↦
    if yzBoundary 0 (⟨(0 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(0 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(0 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(0 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(0 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(0 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(0 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ0]
  rw [kzero _ gm0_0]
  rw [kzero _ gm0_1]
  rw [kzero _ gm0_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb0_0_4_0 (add_le_add cb0_1_3_0 (add_le_add gb0_2 gb0_3))) (le_of_eq (by push_cast; ring)))

theorem hsp1 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 30899268742439042694412418308212000000000000000000000000 := by
  decide +kernel

theorem cb1_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((30899268742439042694412418308212000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.1 30899268742439042694412418308212000000000000000000000000 cm1_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm1_1_3_0 :
    ∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 1495602296323832457375149716504668000000000000000000000000 := by
  decide +kernel

theorem cb1_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((1495602296323832457375149716504668000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.1 1495602296323832457375149716504668000000000000000000000000 cm1_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm1_2_2_0 :
    ∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 802510091511042794918437865187120000000000000000000000000 := by
  decide +kernel

theorem cb1_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((802510091511042794918437865187120000000000000000000000000 * 378233762337668111932220815814 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (1 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378233762337668111932220815814 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.1 802510091511042794918437865187120000000000000000000000000 cm1_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm1_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 30899268742439042694412418308212000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((30899268742439042694412418308212000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.1 30899268742439042694412418308212000000000000000000000000 gm1_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1495602296323832457375149716504668000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1495602296323832457375149716504668000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.1 1495602296323832457375149716504668000000000000000000000000 gm1_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 802510091511042794918437865187120000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb1_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((802510091511042794918437865187120000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((1 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.1 802510091511042794918437865187120000000000000000000000000 gm1_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm1_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(1 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (1 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg1 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (1 : Fin 88)),
            if yzBoundary 0 (⟨(1 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(1 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(1 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((1 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((1 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1917884274473981056495229794991189622250436302475940491108805840000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp1 (fun b ↦
    if yzBoundary 0 (⟨(1 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(1 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(1 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(1 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(1 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ1]
  rw [kzero _ gm1_0]
  rw [kzero _ gm1_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb1_0_4_0 (add_le_add cb1_1_3_0 (add_le_add cb1_2_2_0 (add_le_add gb1_1 (add_le_add gb1_2 gb1_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp2 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25270133588937667182492569105068000000000000000000000000 := by
  decide +kernel

theorem cb2_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25270133588937667182492569105068000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25270133588937667182492569105068000000000000000000000000 cm2_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm2_1_3_0 :
    ∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 4539557603634362159922057769981374000000000000000000000000 := by
  decide +kernel

theorem cb2_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((4539557603634362159922057769981374000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4539557603634362159922057769981374000000000000000000000000 cm2_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm2_2_2_0 :
    ∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 33293901879280911868241883953645189000000000000000000000000 := by
  decide +kernel

theorem cb2_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((33293901879280911868241883953645189000000000000000000000000 * 368704326296747026040022570779 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((368704326296747026040022570779 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33293901879280911868241883953645189000000000000000000000000 cm2_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm2_3_1_0 :
    ∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 939594928910746893184565707268369000000000000000000000000 := by
  decide +kernel

theorem cb2_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(2 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(2 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((939594928910746893184565707268369000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (2 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 939594928910746893184565707268369000000000000000000000000 cm2_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25270133588937667182492569105068000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25270133588937667182492569105068000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25270133588937667182492569105068000000000000000000000000 gm2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4539557603634362159922057769981374000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4539557603634362159922057769981374000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4539557603634362159922057769981374000000000000000000000000 gm2_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33293901879280911868241883953645189000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33293901879280911868241883953645189000000000000000000000000 * 10600122906402954377808391203 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 5 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10600122906402954377808391203 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33293901879280911868241883953645189000000000000000000000000 gm2_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 939594928910746893184565707268369000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb2_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((939594928910746893184565707268369000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((2 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 939594928910746893184565707268369000000000000000000000000 gm2_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm2_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(2 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (2 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg2 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (2 : Fin 88)),
            if yzBoundary 0 (⟨(2 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(2 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(2 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((2 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((2 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((20224243373727418953477177495333461357359331011017491235308672466000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp2 (fun b ↦
    if yzBoundary 0 (⟨(2 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(2 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(2 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(2 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(2 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ2]
  rw [kzero _ gm2_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb2_0_4_0 (add_le_add cb2_1_3_0 (add_le_add cb2_2_2_0 (add_le_add cb2_3_1_0 (add_le_add gb2_0 (add_le_add gb2_1 (add_le_add gb2_2 gb2_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp3 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm3_3_1_0 :
    ∑ w, mu3 3 1 (⟨(3 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84454404040609693729587421634226000000000000000000000000 := by
  decide +kernel

theorem cb3_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(3 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(3 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84454404040609693729587421634226000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (3 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84454404040609693729587421634226000000000000000000000000 cm3_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm3_4_0_0 :
    ∑ w, mu3 3 1 (⟨(3 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25798154354199524632412578365774000000000000000000000000 := by
  decide +kernel

theorem cb3_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(3 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(3 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25798154354199524632412578365774000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (3 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25798154354199524632412578365774000000000000000000000000 cm3_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84454404040609693729587421634226000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb3_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84454404040609693729587421634226000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((3 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84454404040609693729587421634226000000000000000000000000 gm3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25798154354199524632412578365774000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb3_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25798154354199524632412578365774000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((3 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25798154354199524632412578365774000000000000000000000000 gm3_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm3_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm3_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm3_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(3 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (3 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg3 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (3 : Fin 88)),
            if yzBoundary 0 (⟨(3 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(3 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(3 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((3 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((3 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76421250000882739270047516629933281721964865838706000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp3 (fun b ↦
    if yzBoundary 0 (⟨(3 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(3 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(3 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(3 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(3 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(3 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(3 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ3]
  rw [kzero _ gm3_2]
  rw [kzero _ gm3_3]
  rw [kzero _ gm3_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb3_3_1_0 (add_le_add cb3_4_0_0 (add_le_add gb3_0 gb3_1))) (le_of_eq (by push_cast; ring)))

theorem hsp4 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ4 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm4_0_4_0 :
    ∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 638273613978706494475918076612000000000000000000000000 := by
  decide +kernel

theorem cb4_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(4 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((638273613978706494475918076612000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 638273613978706494475918076612000000000000000000000000 cm4_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm4_1_3_0 :
    ∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 75646750617796519596218081464604000000000000000000000000 := by
  decide +kernel

theorem cb4_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((75646750617796519596218081464604000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 75646750617796519596218081464604000000000000000000000000 cm4_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm4_2_2_0 :
    ∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 292645444907787278114204264863804000000000000000000000000 := by
  decide +kernel

theorem cb4_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((292645444907787278114204264863804000000000000000000000000 * 370432070542593824848962606796 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (4 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370432070542593824848962606796 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 292645444907787278114204264863804000000000000000000000000 cm4_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 638273613978706494475918076612000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((638273613978706494475918076612000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 638273613978706494475918076612000000000000000000000000 gm4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 143685313790265636306464002569892000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((143685313790265636306464002569892000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 143685313790265636306464002569892000000000000000000000000 gm4_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1421026549412295460499915893843188000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1421026549412295460499915893843188000000000000000000000000 * 188422932929360541150338443504 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then 7 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((188422932929360541150338443504 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1421026549412295460499915893843188000000000000000000000000 gm4_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 68038563172469116710245921105288000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb4_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((68038563172469116710245921105288000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((4 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 68038563172469116710245921105288000000000000000000000000 gm4_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm4_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(4 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (4 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg4 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (4 : Fin 88)),
            if yzBoundary 0 (⟨(4 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(4 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(4 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((4 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((4 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((575349388585991111788613741124756676991121201256839382873974008000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp4 (fun b ↦
    if yzBoundary 0 (⟨(4 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(4 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(4 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(4 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ4]
  rw [kzero _ gm4_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb4_0_4_0 (add_le_add cb4_1_3_0 (add_le_add cb4_2_2_0 (add_le_add gb4_0 (add_le_add gb4_1 (add_le_add gb4_2 gb4_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp5 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ5 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm5_1_3_0 :
    ∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 811704125585523800956090443765200000000000000000000000000 := by
  decide +kernel

theorem cb5_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((811704125585523800956090443765200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 811704125585523800956090443765200000000000000000000000000 cm5_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm5_2_2_0 :
    ∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 11584324561052082923352356341210400000000000000000000000000 := by
  decide +kernel

theorem cb5_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((11584324561052082923352356341210400000000000000000000000000 * 403515067452509559615459856268 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403515067452509559615459856268 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11584324561052082923352356341210400000000000000000000000000 cm5_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm5_3_1_0 :
    ∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 764485417197761281683488244180200000000000000000000000000 := by
  decide +kernel

theorem cb5_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(5 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(5 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((764485417197761281683488244180200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (5 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 764485417197761281683488244180200000000000000000000000000 cm5_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 918152411268675625568054632557200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((918152411268675625568054632557200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 918152411268675625568054632557200000000000000000000000000 gm5_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33746672573899662942548457123262600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33746672573899662942548457123262600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33746672573899662942548457123262600000000000000000000000000 gm5_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22926833430045341300879589026232400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22926833430045341300879589026232400000000000000000000000000 * 95734781960969432949284909618 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 2 else if k.val = 2 then -6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((95734781960969432949284909618 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22926833430045341300879589026232400000000000000000000000000 gm5_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 106448285683151824611964188792000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb5_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((106448285683151824611964188792000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((5 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106448285683151824611964188792000000000000000000000000000 gm5_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm5_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(5 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (5 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg5 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (5 : Fin 88)),
            if yzBoundary 0 (⟨(5 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(5 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(5 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((5 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((5 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31427071520708753741153029352882799168145736593836655996637910800000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp5 (fun b ↦
    if yzBoundary 0 (⟨(5 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(5 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(5 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(5 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(5 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ5]
  rw [kzero _ gm5_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb5_1_3_0 (add_le_add cb5_2_2_0 (add_le_add cb5_3_1_0 (add_le_add gb5_0 (add_le_add gb5_1 (add_le_add gb5_2 gb5_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp6 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ6 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm6_2_2_0 :
    ∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 4701996321996648076613393979226240000000000000000000000000 := by
  decide +kernel

theorem cb6_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(6 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((4701996321996648076613393979226240000000000000000000000000 * 333711066537444731497739766211 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (6 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((333711066537444731497739766211 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4701996321996648076613393979226240000000000000000000000000 cm6_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm6_3_1_0 :
    ∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 1294168820710372654190372772774080000000000000000000000000 := by
  decide +kernel

theorem cb6_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(6 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((1294168820710372654190372772774080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (6 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1294168820710372654190372772774080000000000000000000000000 cm6_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm6_4_0_0 :
    ∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 10709258598500097065797227248320000000000000000000000000 := by
  decide +kernel

theorem cb6_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(6 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(6 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((10709258598500097065797227248320000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (6 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10709258598500097065797227248320000000000000000000000000 cm6_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5910068646691562904906719781198720000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5910068646691562904906719781198720000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5910068646691562904906719781198720000000000000000000000000 gm6_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 19445821839371618866984593210331840000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((19445821839371618866984593210331840000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 19445821839371618866984593210331840000000000000000000000000 gm6_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1218781583293414925359123029220800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb6_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1218781583293414925359123029220800000000000000000000000000 * 5595650564514853010967361 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((6 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then -5 else if k.val = 2 then 3 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((5595650564514853010967361 : ℚ)/10^30) mme_released_recursive_level3_compat37.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1218781583293414925359123029220800000000000000000000000000 gm6_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm6_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm6_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(6 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (6 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg6 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (6 : Fin 88)),
            if yzBoundary 0 (⟨(6 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(6 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(6 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((6 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((6 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((15944981078219929884112397463824523932674528503265560700656650240000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp6 (fun b ↦
    if yzBoundary 0 (⟨(6 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(6 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(6 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(6 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(6 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(6 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(6 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ6]
  rw [kzero _ gm6_3]
  rw [kzero _ gm6_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb6_2_2_0 (add_le_add cb6_3_1_0 (add_le_add cb6_4_0_0 (add_le_add gb6_0 (add_le_add gb6_1 gb6_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp7 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ7 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm7_3_1_0 :
    ∑ w, mu3 3 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 170723844039969919122146912069790000000000000000000000000 := by
  decide +kernel

theorem cb7_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((170723844039969919122146912069790000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (7 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.1 170723844039969919122146912069790000000000000000000000000 cm7_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm7_4_0_0 :
    ∑ w, mu3 3 1 (⟨(7 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 6944096854350405758680860785233000000000000000000000000 := by
  decide +kernel

theorem cb7_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(7 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(7 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((6944096854350405758680860785233000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (7 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.1 6944096854350405758680860785233000000000000000000000000 cm7_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 478544859573362208800319139214767000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb7_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((478544859573362208800319139214767000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((7 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.1 478544859573362208800319139214767000000000000000000000000 gm7_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 314765112387742695436853087930210000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb7_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((314765112387742695436853087930210000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((7 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.1 314765112387742695436853087930210000000000000000000000000 gm7_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm7_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm7_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm7_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(7 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (7 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg7 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (7 : Fin 88)),
            if yzBoundary 0 (⟨(7 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(7 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(7 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((7 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((7 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((336515301340859136557562883505952327474855510989267000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp7 (fun b ↦
    if yzBoundary 0 (⟨(7 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(7 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(7 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(7 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(7 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(7 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ7]
  rw [kzero _ gm7_2]
  rw [kzero _ gm7_3]
  rw [kzero _ gm7_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb7_3_1_0 (add_le_add cb7_4_0_0 (add_le_add gb7_0 gb7_1))) (le_of_eq (by push_cast; ring)))

theorem hsp8 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ8 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm8_2_2_0 :
    ∑ w, mu3 3 1 (⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 636123456937712651056304322486365000000000000000000000000 := by
  decide +kernel

theorem cb8_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((636123456937712651056304322486365000000000000000000000000 * 398992474582247301840238233313 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (8 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398992474582247301840238233313 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.1 636123456937712651056304322486365000000000000000000000000 cm8_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm8_3_1_0 :
    ∑ w, mu3 3 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 86537930912975341519860742484020000000000000000000000000 := by
  decide +kernel

theorem cb8_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((86537930912975341519860742484020000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (8 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 86537930912975341519860742484020000000000000000000000000 cm8_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9690079448417667467224743557180050000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb8_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9690079448417667467224743557180050000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((8 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.1 9690079448417667467224743557180050000000000000000000000000 gm8_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32992416939877414999900652143155880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb8_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32992416939877414999900652143155880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((8 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.1 32992416939877414999900652143155880000000000000000000000000 gm8_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9053955991479954816168439234693685000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb8_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9053955991479954816168439234693685000000000000000000000000 * 207647154385583603906652293769 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((8 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then 3 else if k.val = 2 then 4 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207647154385583603906652293769 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.1 9053955991479954816168439234693685000000000000000000000000 gm8_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm8_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm8_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(8 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (8 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg8 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (8 : Fin 88)),
            if yzBoundary 0 (⟨(8 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(8 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(8 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((8 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((8 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((25062420974344538503996637052766586352367652576776861855394525760000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp8 (fun b ↦
    if yzBoundary 0 (⟨(8 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(8 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(8 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(8 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(8 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(8 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ8]
  rw [kzero _ gm8_3]
  rw [kzero _ gm8_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb8_2_2_0 (add_le_add cb8_3_1_0 (add_le_add gb8_0 (add_le_add gb8_1 gb8_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp9 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
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
    ∑ w, mu3 3 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 6940234216817860413781166392500000000000000000000000000 := by
  decide +kernel

theorem cb9_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((6940234216817860413781166392500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (9 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6940234216817860413781166392500000000000000000000000000 cm9_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 275355597511812690820626677407500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((275355597511812690820626677407500000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 275355597511812690820626677407500000000000000000000000000 gm9_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10280276764553341341679373322592500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10280276764553341341679373322592500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10280276764553341341679373322592500000000000000000000000000 gm9_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10280276764553341341679373322592500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10280276764553341341679373322592500000000000000000000000000 * 361203185704952269166810465647 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361203185704952269166810465647 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10280276764553341341679373322592500000000000000000000000000 gm9_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 268415363294994830406845511015000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb9_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((268415363294994830406845511015000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((9 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 268415363294994830406845511015000000000000000000000000000 gm9_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm9_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(9 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (9 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg9 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (9 : Fin 88)),
            if yzBoundary 0 (⟨(9 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(9 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(9 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((9 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((9 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((11029875528078043750805611457595599642844469943330048856971700000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp9 (fun b ↦
    if yzBoundary 0 (⟨(9 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(9 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(9 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(9 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ9]
  rw [kzero _ gm9_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb9_1_3_0 (add_le_add gb9_0 (add_le_add gb9_1 (add_le_add gb9_2 gb9_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp10 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ10 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm10_3_1_0 :
    ∑ w, mu3 3 1 (⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 3936048995912699611669057476800000000000000000000000000 := by
  decide +kernel

theorem cb10_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((3936048995912699611669057476800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (10 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3936048995912699611669057476800000000000000000000000000 cm10_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm10_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5986784438117500075072000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb10_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5986784438117500075072000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((10 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5986784438117500075072000000000000000000000000000000000000 gm10_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm10_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5982848389121587375460330942523200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb10_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5982848389121587375460330942523200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((10 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5982848389121587375460330942523200000000000000000000000000 gm10_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm10_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm10_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm10_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(10 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (10 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg10 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (10 : Fin 88)),
            if yzBoundary 0 (⟨(10 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(10 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(10 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((10 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((10 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4149722753901301550301924086350621343766043276975936000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp10 (fun b ↦
    if yzBoundary 0 (⟨(10 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(10 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(10 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(10 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(10 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ10]
  rw [kzero _ gm10_2]
  rw [kzero _ gm10_3]
  rw [kzero _ gm10_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb10_3_1_0 (add_le_add gb10_0 gb10_1)) (le_of_eq (by push_cast; ring)))

theorem hsp11 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
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
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1179630827940643549096549082047476000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1179630827940643549096549082047476000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1179630827940643549096549082047476000000000000000000000000 gm11_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4028629687846097382810901835905048000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4028629687846097382810901835905048000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4028629687846097382810901835905048000000000000000000000000 gm11_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1179630827940643549096549082047476000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb11_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1179630827940643549096549082047476000000000000000000000000 * 424534979354209519420258627686 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((11 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424534979354209519420258627686 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1179630827940643549096549082047476000000000000000000000000 gm11_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm11_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm11_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(11 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (11 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg11 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (11 : Fin 88)),
            if yzBoundary 0 (⟨(11 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(11 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(11 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((11 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((11 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3293227858835985163009556953379939308266097783324203429633783156000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp11 (fun b ↦
    if yzBoundary 0 (⟨(11 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(11 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(11 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(11 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ11]
  rw [kzero _ gm11_3]
  rw [kzero _ gm11_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb11_0 (add_le_add gb11_1 gb11_2)) (le_of_eq (by push_cast; ring)))

theorem hsp12 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2822252391400658937696000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb12_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2822252391400658937696000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((12 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2822252391400658937696000000000000000000000000000000000000 gm12_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm12_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2822252391400658937696000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb12_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2822252391400658937696000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((12 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2822252391400658937696000000000000000000000000000000000000 gm12_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm12_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm12_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm12_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(12 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (12 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg12 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (12 : Fin 88)),
            if yzBoundary 0 (⟨(12 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(12 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(12 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((12 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((12 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1956236287927929981362145841009758879703923734190048000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp12 (fun b ↦
    if yzBoundary 0 (⟨(12 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(12 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(12 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(12 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ12]
  rw [kzero _ gm12_2]
  rw [kzero _ gm12_3]
  rw [kzero _ gm12_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb12_0 gb12_1) (le_of_eq (by push_cast; ring)))

theorem hsp13 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
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

theorem gm13_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111399498228388643496000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb13_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111399498228388643496000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((13 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111399498228388643496000000000000000000000000000000000000 gm13_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm13_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111399498228388643496000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb13_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111399498228388643496000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((13 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111399498228388643496000000000000000000000000000000000000 gm13_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm13_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm13_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm13_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(13 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (13 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg13 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (13 : Fin 88)),
            if yzBoundary 0 (⟨(13 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(13 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(13 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((13 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((13 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((77216248112800210687697319680232032632735620365448000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp13 (fun b ↦
    if yzBoundary 0 (⟨(13 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(13 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(13 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(13 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ13]
  rw [kzero _ gm13_2]
  rw [kzero _ gm13_3]
  rw [kzero _ gm13_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb13_0 gb13_1) (le_of_eq (by push_cast; ring)))

theorem hsp14 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25808681866625590319458554259800000000000000000000000000 := by
  decide +kernel

theorem cb14_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25808681866625590319458554259800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25808681866625590319458554259800000000000000000000000000 cm14_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm14_1_3_0 :
    ∑ w, mu3 3 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84445348626205106280541445740200000000000000000000000000 := by
  decide +kernel

theorem cb14_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84445348626205106280541445740200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (14 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84445348626205106280541445740200000000000000000000000000 cm14_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm14_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm14_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25808681866625590319458554259800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25808681866625590319458554259800000000000000000000000000 * 179757089306214982506970510960 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -5 else if k.val = 2 then -2 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((179757089306214982506970510960 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25808681866625590319458554259800000000000000000000000000 gm14_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84445348626205106280541445740200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb14_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84445348626205106280541445740200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((14 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84445348626205106280541445740200000000000000000000000000 gm14_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm14_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(14 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (14 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg14 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (14 : Fin 88)),
            if yzBoundary 0 (⟨(14 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(14 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(14 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((14 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((14 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((121705404154486148205657415674495236750563397119478131016109000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp14 (fun b ↦
    if yzBoundary 0 (⟨(14 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(14 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(14 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(14 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(14 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ14]
  rw [kzero _ gm14_0]
  rw [kzero _ gm14_1]
  rw [kzero _ gm14_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb14_0_4_0 (add_le_add cb14_1_3_0 (add_le_add gb14_2 gb14_3))) (le_of_eq (by push_cast; ring)))

theorem hsp15 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
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
    ∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 29098658919690281986880164929318000000000000000000000000 := by
  decide +kernel

theorem cb15_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((29098658919690281986880164929318000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 29098658919690281986880164929318000000000000000000000000 cm15_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm15_1_3_0 :
    ∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 1314027507392495144818063590005352000000000000000000000000 := by
  decide +kernel

theorem cb15_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((1314027507392495144818063590005352000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.1 1314027507392495144818063590005352000000000000000000000000 cm15_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm15_2_2_0 :
    ∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 724238884420220220009056245065330000000000000000000000000 := by
  decide +kernel

theorem cb15_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((724238884420220220009056245065330000000000000000000000000 * 412477706764252046980066481716 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (15 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then -2 else if k.val = 2 then 1 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((412477706764252046980066481716 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.1 724238884420220220009056245065330000000000000000000000000 cm15_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm15_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29098658919690281986880164929318000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29098658919690281986880164929318000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.1 29098658919690281986880164929318000000000000000000000000 gm15_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1314027507392495144818063590005352000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1314027507392495144818063590005352000000000000000000000000 * 157530828511045725373479806 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then -7 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((157530828511045725373479806 : ℚ)/10^30) mme_released_recursive_level3_compat39.1 1314027507392495144818063590005352000000000000000000000000 gm15_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 724238884420220220009056245065330000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb15_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((724238884420220220009056245065330000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((15 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat38.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 724238884420220220009056245065330000000000000000000000000 gm15_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm15_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(15 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (15 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg15 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (15 : Fin 88)),
            if yzBoundary 0 (⟨(15 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(15 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(15 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((15 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((15 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1731927650140413742022619737187182627125397439940319083228933218000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp15 (fun b ↦
    if yzBoundary 0 (⟨(15 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(15 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(15 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(15 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(15 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ15]
  rw [kzero _ gm15_0]
  rw [kzero _ gm15_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb15_0_4_0 (add_le_add cb15_1_3_0 (add_le_add cb15_2_2_0 (add_le_add gb15_1 (add_le_add gb15_2 gb15_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp16 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 21603271001362594510708163911608000000000000000000000000 := by
  decide +kernel

theorem cb16_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((21603271001362594510708163911608000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.1 21603271001362594510708163911608000000000000000000000000 cm16_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm16_1_3_0 :
    ∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 4175901384652983527301207499288776000000000000000000000000 := by
  decide +kernel

theorem cb16_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((4175901384652983527301207499288776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.1 4175901384652983527301207499288776000000000000000000000000 cm16_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm16_2_2_0 :
    ∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 28325763543524079174970593296456325000000000000000000000000 := by
  decide +kernel

theorem cb16_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((28325763543524079174970593296456325000000000000000000000000 * 377361931182870694302174937337 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((377361931182870694302174937337 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28325763543524079174970593296456325000000000000000000000000 cm16_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm16_3_1_0 :
    ∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 816071584681833028898491040343291000000000000000000000000 := by
  decide +kernel

theorem cb16_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((816071584681833028898491040343291000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (16 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 816071584681833028898491040343291000000000000000000000000 cm16_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21603271001362594510708163911608000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21603271001362594510708163911608000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21603271001362594510708163911608000000000000000000000000 gm16_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4175901384652983527301207499288776000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4175901384652983527301207499288776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.1 4175901384652983527301207499288776000000000000000000000000 gm16_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 28325763543524079174970593296456325000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((28325763543524079174970593296456325000000000000000000000000 * 18682811408613560360261386217 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((18682811408613560360261386217 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.1 28325763543524079174970593296456325000000000000000000000000 gm16_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 816071584681833028898491040343291000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb16_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((816071584681833028898491040343291000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((16 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.1 816071584681833028898491040343291000000000000000000000000 gm16_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm16_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(16 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (16 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg16 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (16 : Fin 88)),
            if yzBoundary 0 (⟨(16 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(16 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(16 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((16 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((16 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((18138613709554015686252112242278842310541901077390800267322126366000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp16 (fun b ↦
    if yzBoundary 0 (⟨(16 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(16 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(16 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(16 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(16 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ16]
  rw [kzero _ gm16_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb16_0_4_0 (add_le_add cb16_1_3_0 (add_le_add cb16_2_2_0 (add_le_add cb16_3_1_0 (add_le_add gb16_0 (add_le_add gb16_1 (add_le_add gb16_2 gb16_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp17 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84482294228396880770092620729520000000000000000000000000 := by
  decide +kernel

theorem cb17_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84482294228396880770092620729520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (17 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84482294228396880770092620729520000000000000000000000000 cm17_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm17_4_0_0 :
    ∑ w, mu3 3 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25117504966169512109907379270480000000000000000000000000 := by
  decide +kernel

theorem cb17_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25117504966169512109907379270480000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (17 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25117504966169512109907379270480000000000000000000000000 cm17_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84482294228396880770092620729520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb17_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84482294228396880770092620729520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((17 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84482294228396880770092620729520000000000000000000000000 gm17_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25117504966169512109907379270480000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb17_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25117504966169512109907379270480000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((17 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25117504966169512109907379270480000000000000000000000000 gm17_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm17_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm17_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm17_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(17 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (17 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg17 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (17 : Fin 88)),
            if yzBoundary 0 (⟨(17 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(17 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(17 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((17 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((17 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((75968791801649860019612161400978317110030403107440000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp17 (fun b ↦
    if yzBoundary 0 (⟨(17 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(17 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(17 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(17 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(17 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(17 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ17]
  rw [kzero _ gm17_2]
  rw [kzero _ gm17_3]
  rw [kzero _ gm17_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb17_3_1_0 (add_le_add cb17_4_0_0 (add_le_add gb17_0 gb17_1))) (le_of_eq (by push_cast; ring)))

theorem hsp18 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ18 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm18_0_4_0 :
    ∑ w, mu3 3 1 (⟨(18 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 7585485632997350355010462057868000000000000000000000000 := by
  decide +kernel

theorem cb18_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(18 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(18 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((7585485632997350355010462057868000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (18 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7585485632997350355010462057868000000000000000000000000 cm18_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm18_1_3_0 :
    ∑ w, mu3 3 1 (⟨(18 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 186044804088090610009562263880216000000000000000000000000 := by
  decide +kernel

theorem cb18_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(18 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(18 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((186044804088090610009562263880216000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (18 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 186044804088090610009562263880216000000000000000000000000 cm18_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm18_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7585485632997350355010462057868000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7585485632997350355010462057868000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7585485632997350355010462057868000000000000000000000000 gm18_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 521464065767319711528989537942132000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((521464065767319711528989537942132000000000000000000000000 * 227741837116757344728819757399 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((227741837116757344728819757399 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 521464065767319711528989537942132000000000000000000000000 gm18_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 335419261679229101519427274061916000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb18_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((335419261679229101519427274061916000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((18 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 335419261679229101519427274061916000000000000000000000000 gm18_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm18_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(18 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (18 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg18 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (18 : Fin 88)),
            if yzBoundary 0 (⟨(18 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(18 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(18 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((18 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((18 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((485468389257856602667087980063771858314303232239790823175239744000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp18 (fun b ↦
    if yzBoundary 0 (⟨(18 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(18 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(18 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(18 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(18 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(18 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ18]
  rw [kzero _ gm18_0]
  rw [kzero _ gm18_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb18_0_4_0 (add_le_add cb18_1_3_0 (add_le_add gb18_1 (add_le_add gb18_2 gb18_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp19 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ19 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm19_0_4_0 :
    ∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 4710708793981727750233319056917000000000000000000000000 := by
  decide +kernel

theorem cb19_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(19 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((4710708793981727750233319056917000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4710708793981727750233319056917000000000000000000000000 cm19_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm19_1_3_0 :
    ∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 577250731616131335525430803723690000000000000000000000000 := by
  decide +kernel

theorem cb19_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((577250731616131335525430803723690000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 577250731616131335525430803723690000000000000000000000000 cm19_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm19_2_2_0 :
    ∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 2068454727209682987672961661870763000000000000000000000000 := by
  decide +kernel

theorem cb19_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((2068454727209682987672961661870763000000000000000000000000 * 374844535000613121452432329496 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (19 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((374844535000613121452432329496 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2068454727209682987672961661870763000000000000000000000000 cm19_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4710708793981727750233319056917000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4710708793981727750233319056917000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4710708793981727750233319056917000000000000000000000000 gm19_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1091628525575237472462089155119198000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1091628525575237472462089155119198000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1091628525575237472462089155119198000000000000000000000000 gm19_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10067619981487655758596393389777007000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10067619981487655758596393389777007000000000000000000000000 * 202646540066185752432134051039 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((202646540066185752432134051039 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10067619981487655758596393389777007000000000000000000000000 gm19_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 514377793959106136936658351395508000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb19_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((514377793959106136936658351395508000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((19 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 514377793959106136936658351395508000000000000000000000000 gm19_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm19_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(19 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (19 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg19 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (19 : Fin 88)),
            if yzBoundary 0 (⟨(19 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(19 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(19 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((19 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((19 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4328835775782976185623159621213873906293993200336604163747812935000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp19 (fun b ↦
    if yzBoundary 0 (⟨(19 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(19 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(19 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(19 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ19]
  rw [kzero _ gm19_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb19_0_4_0 (add_le_add cb19_1_3_0 (add_le_add cb19_2_2_0 (add_le_add gb19_0 (add_le_add gb19_1 (add_le_add gb19_2 gb19_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp20 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ20 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm20_1_3_0 :
    ∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 717836632403570913208999650145792000000000000000000000000 := by
  decide +kernel

theorem cb20_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((717836632403570913208999650145792000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 717836632403570913208999650145792000000000000000000000000 cm20_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm20_2_2_0 :
    ∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 10169376069730216872678611599179776000000000000000000000000 := by
  decide +kernel

theorem cb20_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((10169376069730216872678611599179776000000000000000000000000 * 403048178985424984142134147353 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403048178985424984142134147353 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10169376069730216872678611599179776000000000000000000000000 cm20_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm20_3_1_0 :
    ∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 667455523928064387223663938607424000000000000000000000000 := by
  decide +kernel

theorem cb20_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(20 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(20 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((667455523928064387223663938607424000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (20 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 667455523928064387223663938607424000000000000000000000000 cm20_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 811432902996243872062637457604800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((811432902996243872062637457604800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 811432902996243872062637457604800000000000000000000000000 gm20_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29630316846446246321641698603787776000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29630316846446246321641698603787776000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29630316846446246321641698603787776000000000000000000000000 gm20_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20128396300644093836186750943215424000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20128396300644093836186750943215424000000000000000000000000 * 96900099737423934162372652939 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((96900099737423934162372652939 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 20128396300644093836186750943215424000000000000000000000000 gm20_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 93596270592672958853637807459008000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb20_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((93596270592672958853637807459008000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((20 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 93596270592672958853637807459008000000000000000000000000 gm20_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm20_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(20 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (20 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg20 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (20 : Fin 88)),
            if yzBoundary 0 (⟨(20 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(20 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(20 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((20 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((20 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27612450040106912334547387977028717213401956063013628655988497664000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp20 (fun b ↦
    if yzBoundary 0 (⟨(20 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(20 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(20 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(20 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(20 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ20]
  rw [kzero _ gm20_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb20_1_3_0 (add_le_add cb20_2_2_0 (add_le_add cb20_3_1_0 (add_le_add gb20_0 (add_le_add gb20_1 (add_le_add gb20_2 gb20_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp21 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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
    ∑ w, mu3 3 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 545432701170796556642362037290640000000000000000000000000 := by
  decide +kernel

theorem cb21_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((545432701170796556642362037290640000000000000000000000000 * 398418774763504077382095240459 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (21 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398418774763504077382095240459 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 545432701170796556642362037290640000000000000000000000000 cm21_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm21_3_1_0 :
    ∑ w, mu3 3 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 73796759185195346165536676721408000000000000000000000000 := by
  decide +kernel

theorem cb21_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((73796759185195346165536676721408000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (21 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 73796759185195346165536676721408000000000000000000000000 cm21_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8303269888902554287746621783353816000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8303269888902554287746621783353816000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8303269888902554287746621783353816000000000000000000000000 gm21_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 28286680733527388623437219756570960000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((28286680733527388623437219756570960000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28286680733527388623437219756570960000000000000000000000000 gm21_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7757837187731757731104259746063176000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb21_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7757837187731757731104259746063176000000000000000000000000 * 207726836941812878727542840527 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((21 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207726836941812878727542840527 : ℚ)/10^30) mme_released_recursive_level3_compat39.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7757837187731757731104259746063176000000000000000000000000 gm21_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm21_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm21_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(21 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (21 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg21 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (21 : Fin 88)),
            if yzBoundary 0 (⟨(21 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(21 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(21 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((21 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((21 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((21486806622441018718581139657570178044481986110529964457132368432000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp21 (fun b ↦
    if yzBoundary 0 (⟨(21 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(21 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(21 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(21 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(21 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(21 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ21]
  rw [kzero _ gm21_3]
  rw [kzero _ gm21_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb21_2_2_0 (add_le_add cb21_3_1_0 (add_le_add gb21_0 (add_le_add gb21_1 gb21_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp22 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ22 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm22_1_3_0 :
    ∑ w, mu3 3 1 (⟨(22 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 6946223601437266862388669824000000000000000000000000000 := by
  decide +kernel

theorem cb22_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(22 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(22 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((6946223601437266862388669824000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (22 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.1 6946223601437266862388669824000000000000000000000000000 cm22_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 275637344752584202131086015610240000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((275637344752584202131086015610240000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.1 275637344752584202131086015610240000000000000000000000000 gm22_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10245656762205615921388913984389760000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10245656762205615921388913984389760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.1 10245656762205615921388913984389760000000000000000000000000 gm22_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10245656762205615921388913984389760000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10245656762205615921388913984389760000000000000000000000000 * 361616946976262848268381457680 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361616946976262848268381457680 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.1 10245656762205615921388913984389760000000000000000000000000 gm22_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 268691121151146935268697345786240000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb22_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((268691121151146935268697345786240000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((22 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.1 268691121151146935268697345786240000000000000000000000000 gm22_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm22_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(22 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (22 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg22 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (22 : Fin 88)),
            if yzBoundary 0 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((22 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((22 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((10997808464195541184276652007072486805636545115115178156174628480000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp22 (fun b ↦
    if yzBoundary 0 (⟨(22 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(22 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(22 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(22 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ22]
  rw [kzero _ gm22_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb22_1_3_0 (add_le_add gb22_0 (add_le_add gb22_1 (add_le_add gb22_2 gb22_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp23 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ23 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm23_3_1_0 :
    ∑ w, mu3 3 1 (⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 3855240683980223712105625783950000000000000000000000000 := by
  decide +kernel

theorem cb23_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((3855240683980223712105625783950000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (23 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3855240683980223712105625783950000000000000000000000000 cm23_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5885273584830393740685000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5885273584830393740685000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5885273584830393740685000000000000000000000000000000000000 gm23_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5881418344146413516972894374216050000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb23_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5881418344146413516972894374216050000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((23 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5881418344146413516972894374216050000000000000000000000000 gm23_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm23_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm23_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(23 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (23 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg23 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (23 : Fin 88)),
            if yzBoundary 0 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((23 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((23 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4079360792149109538108381907715576424875019723628905000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp23 (fun b ↦
    if yzBoundary 0 (⟨(23 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(23 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(23 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(23 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(23 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ23]
  rw [kzero _ gm23_2]
  rw [kzero _ gm23_3]
  rw [kzero _ gm23_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb23_3_1_0 (add_le_add gb23_0 gb23_1)) (le_of_eq (by push_cast; ring)))

theorem hsp24 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ24 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm24_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1161883679561111074139308953994745000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1161883679561111074139308953994745000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1161883679561111074139308953994745000000000000000000000000 gm24_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3969684036561023447391382092010510000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3969684036561023447391382092010510000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3969684036561023447391382092010510000000000000000000000000 gm24_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1161883679561111074139308953994745000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb24_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1161883679561111074139308953994745000000000000000000000000 * 424645025149394892342246783239 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((24 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424645025149394892342246783239 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1161883679561111074139308953994745000000000000000000000000 gm24_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm24_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm24_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(24 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (24 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg24 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (24 : Fin 88)),
            if yzBoundary 0 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((24 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((24 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3244963421983995744941937057044366723286695323706365889220105330000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp24 (fun b ↦
    if yzBoundary 0 (⟨(24 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(24 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(24 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(24 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ24]
  rw [kzero _ gm24_3]
  rw [kzero _ gm24_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb24_0 (add_le_add gb24_1 gb24_2)) (le_of_eq (by push_cast; ring)))

theorem hsp25 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ25 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm25_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2840772159474113391315000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2840772159474113391315000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2840772159474113391315000000000000000000000000000000000000 gm25_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2840772159474113391315000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb25_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2840772159474113391315000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((25 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2840772159474113391315000000000000000000000000000000000000 gm25_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm25_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm25_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm25_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(25 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (25 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg25 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (25 : Fin 88)),
            if yzBoundary 0 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((25 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((25 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1969073212952669026010822332551708382006694869087095000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp25 (fun b ↦
    if yzBoundary 0 (⟨(25 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(25 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(25 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(25 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ25]
  rw [kzero _ gm25_2]
  rw [kzero _ gm25_3]
  rw [kzero _ gm25_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb25_0 gb25_1) (le_of_eq (by push_cast; ring)))

theorem hsp26 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ26 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm26_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111393274900139108910000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111393274900139108910000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111393274900139108910000000000000000000000000000000000000 gm26_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111393274900139108910000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb26_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111393274900139108910000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((26 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111393274900139108910000000000000000000000000000000000000 gm26_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm26_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm26_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm26_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(26 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (26 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg26 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (26 : Fin 88)),
            if yzBoundary 0 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((26 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((26 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((77211934430370346729636661549452456591547838415830000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp26 (fun b ↦
    if yzBoundary 0 (⟨(26 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(26 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(26 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(26 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ26]
  rw [kzero _ gm26_2]
  rw [kzero _ gm26_3]
  rw [kzero _ gm26_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb26_0 gb26_1) (le_of_eq (by push_cast; ring)))

theorem hsp27 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ27 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm27_0_4_0 :
    ∑ w, mu3 3 1 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25069826743568704210905357916800000000000000000000000000 := by
  decide +kernel

theorem cb27_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25069826743568704210905357916800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25069826743568704210905357916800000000000000000000000000 cm27_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm27_1_3_0 :
    ∑ w, mu3 3 1 (⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84626180192718055389094642083200000000000000000000000000 := by
  decide +kernel

theorem cb27_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84626180192718055389094642083200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (27 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84626180192718055389094642083200000000000000000000000000 cm27_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm27_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25069826743568704210905357916800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25069826743568704210905357916800000000000000000000000000 * 21757250307511361091493088 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((21757250307511361091493088 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25069826743568704210905357916800000000000000000000000000 gm27_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84626180192718055389094642083200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb27_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84626180192718055389094642083200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((27 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84626180192718055389094642083200000000000000000000000000 gm27_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm27_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(27 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (27 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg27 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (27 : Fin 88)),
            if yzBoundary 0 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((27 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((27 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117317341854776444328423495504189739012221104239581397689494400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp27 (fun b ↦
    if yzBoundary 0 (⟨(27 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(27 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(27 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(27 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(27 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(27 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ27]
  rw [kzero _ gm27_0]
  rw [kzero _ gm27_1]
  rw [kzero _ gm27_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb27_0_4_0 (add_le_add cb27_1_3_0 (add_le_add gb27_2 gb27_3))) (le_of_eq (by push_cast; ring)))

theorem hsp28 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ28 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm28_0_4_0 :
    ∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 31171048084383390189087656832378000000000000000000000000 := by
  decide +kernel

theorem cb28_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((31171048084383390189087656832378000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31171048084383390189087656832378000000000000000000000000 cm28_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_1_3_0 :
    ∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 1508242961506205187113043160210056000000000000000000000000 := by
  decide +kernel

theorem cb28_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((1508242961506205187113043160210056000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1508242961506205187113043160210056000000000000000000000000 cm28_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm28_2_2_0 :
    ∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 809150863246463857383869182957566000000000000000000000000 := by
  decide +kernel

theorem cb28_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((809150863246463857383869182957566000000000000000000000000 * 378292400856232771227952197649 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (28 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378292400856232771227952197649 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 809150863246463857383869182957566000000000000000000000000 cm28_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm28_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 31171048084383390189087656832378000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((31171048084383390189087656832378000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31171048084383390189087656832378000000000000000000000000 gm28_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1508242961506205187113043160210056000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1508242961506205187113043160210056000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1508242961506205187113043160210056000000000000000000000000 gm28_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 809150863246463857383869182957566000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb28_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((809150863246463857383869182957566000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((28 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 809150863246463857383869182957566000000000000000000000000 gm28_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm28_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(28 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (28 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg28 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (28 : Fin 88)),
            if yzBoundary 0 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((28 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((28 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1933996742681527469123934001855556534301865680302520142931259372000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp28 (fun b ↦
    if yzBoundary 0 (⟨(28 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(28 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(28 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(28 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(28 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ28]
  rw [kzero _ gm28_0]
  rw [kzero _ gm28_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb28_0_4_0 (add_le_add cb28_1_3_0 (add_le_add cb28_2_2_0 (add_le_add gb28_1 (add_le_add gb28_2 gb28_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp29 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ29 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm29_0_4_0 :
    ∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25156463520659099889157204596608000000000000000000000000 := by
  decide +kernel

theorem cb29_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25156463520659099889157204596608000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25156463520659099889157204596608000000000000000000000000 cm29_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_1_3_0 :
    ∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 4477087064861342026632215725509540000000000000000000000000 := by
  decide +kernel

theorem cb29_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((4477087064861342026632215725509540000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4477087064861342026632215725509540000000000000000000000000 cm29_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_2_2_0 :
    ∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 32884739234776446686242936255898576000000000000000000000000 := by
  decide +kernel

theorem cb29_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(29 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((32884739234776446686242936255898576000000000000000000000000 * 369079267589300021405593728854 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -2 else if k.val = 2 then -6 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((369079267589300021405593728854 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32884739234776446686242936255898576000000000000000000000000 cm29_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm29_3_1_0 :
    ∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 935548882082373706567690813995276000000000000000000000000 := by
  decide +kernel

theorem cb29_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((935548882082373706567690813995276000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (29 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 935548882082373706567690813995276000000000000000000000000 cm29_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25156463520659099889157204596608000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25156463520659099889157204596608000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25156463520659099889157204596608000000000000000000000000 gm29_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4477087064861342026632215725509540000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4477087064861342026632215725509540000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4477087064861342026632215725509540000000000000000000000000 gm29_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32884739234776446686242936255898576000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32884739234776446686242936255898576000000000000000000000000 * 10480829957285506158095124783 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10480829957285506158095124783 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32884739234776446686242936255898576000000000000000000000000 gm29_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 935548882082373706567690813995276000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb29_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((935548882082373706567690813995276000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((29 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 935548882082373706567690813995276000000000000000000000000 gm29_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm29_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(29 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (29 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg29 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (29 : Fin 88)),
            if yzBoundary 0 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((29 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((29 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((19985241523788668999507088131523839709295187008893446052375131216000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp29 (fun b ↦
    if yzBoundary 0 (⟨(29 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(29 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(29 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(29 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(29 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ29]
  rw [kzero _ gm29_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb29_0_4_0 (add_le_add cb29_1_3_0 (add_le_add cb29_2_2_0 (add_le_add cb29_3_1_0 (add_le_add gb29_0 (add_le_add gb29_1 (add_le_add gb29_2 gb29_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp30 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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
    ∑ w, mu3 3 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84514676201238131937124848881685000000000000000000000000 := by
  decide +kernel

theorem cb30_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84514676201238131937124848881685000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.1 84514676201238131937124848881685000000000000000000000000 cm30_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm30_4_0_0 :
    ∑ w, mu3 3 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 26272942162270627427875151118315000000000000000000000000 := by
  decide +kernel

theorem cb30_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((26272942162270627427875151118315000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (30 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.1 26272942162270627427875151118315000000000000000000000000 cm30_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84514676201238131937124848881685000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84514676201238131937124848881685000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.1 84514676201238131937124848881685000000000000000000000000 gm30_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26272942162270627427875151118315000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb30_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26272942162270627427875151118315000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((30 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat40.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 26272942162270627427875151118315000000000000000000000000 gm30_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm30_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm30_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(30 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (30 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg30 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (30 : Fin 88)),
            if yzBoundary 0 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((30 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((30 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76792125309617318703301577660943658019862658871745000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp30 (fun b ↦
    if yzBoundary 0 (⟨(30 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(30 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(30 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(30 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(30 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(30 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(30 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ30]
  rw [kzero _ gm30_2]
  rw [kzero _ gm30_3]
  rw [kzero _ gm30_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb30_3_1_0 (add_le_add cb30_4_0_0 (add_le_add gb30_0 gb30_1))) (le_of_eq (by push_cast; ring)))

theorem hsp31 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 476316799549535696031910271880000000000000000000000000 := by
  decide +kernel

theorem cb31_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((476316799549535696031910271880000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.1 476316799549535696031910271880000000000000000000000000 cm31_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm31_1_3_0 :
    ∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 56384220405446447722760574299984000000000000000000000000 := by
  decide +kernel

theorem cb31_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((56384220405446447722760574299984000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.1 56384220405446447722760574299984000000000000000000000000 cm31_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm31_2_2_0 :
    ∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 218283752362118395142464412457564000000000000000000000000 := by
  decide +kernel

theorem cb31_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((218283752362118395142464412457564000000000000000000000000 * 370509915745904919030216150749 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (31 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -5 else if k.val = 2 then 4 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370509915745904919030216150749 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.1 218283752362118395142464412457564000000000000000000000000 cm31_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 476316799549535696031910271880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((476316799549535696031910271880000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.1 476316799549535696031910271880000000000000000000000000 gm31_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 107188914034726401313835451633392000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((107188914034726401313835451633392000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.1 107188914034726401313835451633392000000000000000000000000 gm31_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1059951246714686039721800863731892000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1059951246714686039721800863731892000000000000000000000000 * 188310211532032656397217014206 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -3 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((188310211532032656397217014206 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.1 1059951246714686039721800863731892000000000000000000000000 gm31_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 50804693629279953591074877333408000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb31_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((50804693629279953591074877333408000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((31 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.1 50804693629279953591074877333408000000000000000000000000 gm31_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm31_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(31 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (31 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg31 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (31 : Fin 88)),
            if yzBoundary 0 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((31 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((31 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((429071325279778636370382440543225193850311447632024042963980212000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp31 (fun b ↦
    if yzBoundary 0 (⟨(31 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(31 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(31 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(31 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(31 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(31 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(31 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ31]
  rw [kzero _ gm31_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb31_0_4_0 (add_le_add cb31_1_3_0 (add_le_add cb31_2_2_0 (add_le_add gb31_0 (add_le_add gb31_1 (add_le_add gb31_2 gb31_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp32 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
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
    ∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 872344811431024342620504090314409000000000000000000000000 := by
  decide +kernel

theorem cb32_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((872344811431024342620504090314409000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 872344811431024342620504090314409000000000000000000000000 cm32_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm32_2_2_0 :
    ∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 12462716553820972750839817716356493000000000000000000000000 := by
  decide +kernel

theorem cb32_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((12462716553820972750839817716356493000000000000000000000000 * 404151490939362918897062657869 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -8 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-15 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((404151490939362918897062657869 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12462716553820972750839817716356493000000000000000000000000 cm32_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm32_3_1_0 :
    ∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 829352853296709076378208971956717000000000000000000000000 := by
  decide +kernel

theorem cb32_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((829352853296709076378208971956717000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (32 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 829352853296709076378208971956717000000000000000000000000 cm32_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 987722227317525601011022279324665000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((987722227317525601011022279324665000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 987722227317525601011022279324665000000000000000000000000 gm32_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 36303309948768253109857768748718618000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((36303309948768253109857768748718618000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 36303309948768253109857768748718618000000000000000000000000 gm32_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 24669946248243989435396160004318842000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((24669946248243989435396160004318842000000000000000000000000 * 95460562499330568765533787852 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 4 else if k.val = 2 then 4 else -7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((95460562499330568765533787852 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24669946248243989435396160004318842000000000000000000000000 gm32_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 115377415886501258390518189010256000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb32_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((115377415886501258390518189010256000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((32 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 115377415886501258390518189010256000000000000000000000000 gm32_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm32_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(32 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (32 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg32 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (32 : Fin 88)),
            if yzBoundary 0 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((32 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((32 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((33814869827043065507557451325678626208694944973451286516645273456000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp32 (fun b ↦
    if yzBoundary 0 (⟨(32 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(32 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(32 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(32 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(32 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(32 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(32 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ32]
  rw [kzero _ gm32_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb32_1_3_0 (add_le_add cb32_2_2_0 (add_le_add cb32_3_1_0 (add_le_add gb32_0 (add_le_add gb32_1 (add_le_add gb32_2 gb32_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp33 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ33 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm33_2_2_0 :
    ∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 7973911786854366731146467168501192000000000000000000000000 := by
  decide +kernel

theorem cb33_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((7973911786854366731146467168501192000000000000000000000000 * 340000902000109392253604180901 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((340000902000109392253604180901 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7973911786854366731146467168501192000000000000000000000000 cm33_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_3_1_0 :
    ∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 2304082761994063458011594496062340000000000000000000000000 := by
  decide +kernel

theorem cb33_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((2304082761994063458011594496062340000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2304082761994063458011594496062340000000000000000000000000 cm33_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm33_4_0_0 :
    ∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 18727400692503720062433252790020000000000000000000000000 := by
  decide +kernel

theorem cb33_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((18727400692503720062433252790020000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (33 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18727400692503720062433252790020000000000000000000000000 cm33_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10122666490718746179805807964277930000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10122666490718746179805807964277930000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10122666490718746179805807964277930000000000000000000000000 gm33_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33171002410352440227537923069801760000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33171002410352440227537923069801760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33171002410352440227537923069801760000000000000000000000000 gm33_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2167482104556883168721774048566758000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb33_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2167482104556883168721774048566758000000000000000000000000 * 11171606600625896999436660 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((33 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else 5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((11171606600625896999436660 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2167482104556883168721774048566758000000000000000000000000 gm33_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm33_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm33_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(33 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (33 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg33 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (33 : Fin 88)),
            if yzBoundary 0 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((33 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((33 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27300616681593075277526136291877254033094547144664287780619342522000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp33 (fun b ↦
    if yzBoundary 0 (⟨(33 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(33 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(33 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(33 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(33 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(33 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(33 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ33]
  rw [kzero _ gm33_3]
  rw [kzero _ gm33_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb33_2_2_0 (add_le_add cb33_3_1_0 (add_le_add cb33_4_0_0 (add_le_add gb33_0 (add_le_add gb33_1 gb33_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp34 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm34_3_1_0 :
    ∑ w, mu3 3 1 (⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 320617729560508479511131808033374000000000000000000000000 := by
  decide +kernel

theorem cb34_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((320617729560508479511131808033374000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (34 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 320617729560508479511131808033374000000000000000000000000 cm34_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm34_4_0_0 :
    ∑ w, mu3 3 1 (⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 13253806772464293708286785421536000000000000000000000000 := by
  decide +kernel

theorem cb34_4_0_0 :
    ((∑ w, mu3 3 1 (⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((13253806772464293708286785421536000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (34 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13253806772464293708286785421536000000000000000000000000 cm34_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 892677196556917025009713214578464000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((892677196556917025009713214578464000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 892677196556917025009713214578464000000000000000000000000 gm34_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 585313273768872839206868191966626000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb34_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((585313273768872839206868191966626000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((34 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 585313273768872839206868191966626000000000000000000000000 gm34_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm34_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm34_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm34_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(34 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (34 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg34 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (34 : Fin 88)),
            if yzBoundary 0 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((34 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((34 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((627943520739603088183997676852282852657949251143334000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp34 (fun b ↦
    if yzBoundary 0 (⟨(34 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(34 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(34 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(34 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(34 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(34 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ34]
  rw [kzero _ gm34_2]
  rw [kzero _ gm34_3]
  rw [kzero _ gm34_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb34_3_1_0 (add_le_add cb34_4_0_0 (add_le_add gb34_0 gb34_1))) (le_of_eq (by push_cast; ring)))

theorem hsp35 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ35 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm35_2_2_0 :
    ∑ w, mu3 3 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 801254765399757670426024054454280000000000000000000000000 := by
  decide +kernel

theorem cb35_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((801254765399757670426024054454280000000000000000000000000 * 399697609135331146815953433696 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 7 else if k.val = 2 then 5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((399697609135331146815953433696 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 801254765399757670426024054454280000000000000000000000000 cm35_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm35_3_1_0 :
    ∑ w, mu3 3 1 (⟨(35 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 110001906286936139576068813424144000000000000000000000000 := by
  decide +kernel

theorem cb35_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(35 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(35 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((110001906286936139576068813424144000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (35 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 110001906286936139576068813424144000000000000000000000000 cm35_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12320063858552378221045430838773912000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12320063858552378221045430838773912000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12320063858552378221045430838773912000000000000000000000000 gm35_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 41953839087628727403309069509028032000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((41953839087628727403309069509028032000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 41953839087628727403309069509028032000000000000000000000000 gm35_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11518809093152620550619406784319632000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb35_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11518809093152620550619406784319632000000000000000000000000 * 207797320146130077229393210137 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((35 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 5 else if k.val = 2 then 0 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207797320146130077229393210137 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11518809093152620550619406784319632000000000000000000000000 gm35_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm35_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm35_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(35 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (35 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg35 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (35 : Fin 88)),
            if yzBoundary 0 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((35 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((35 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31870270063325052963305693639446447771152325672690023824208058904000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp35 (fun b ↦
    if yzBoundary 0 (⟨(35 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(35 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(35 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(35 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(35 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(35 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ35]
  rw [kzero _ gm35_3]
  rw [kzero _ gm35_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb35_2_2_0 (add_le_add cb35_3_1_0 (add_le_add gb35_0 (add_le_add gb35_1 gb35_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp36 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ36 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm36_1_3_0 :
    ∑ w, mu3 3 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 6113094875102378278727208078196000000000000000000000000 := by
  decide +kernel

theorem cb36_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((6113094875102378278727208078196000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (36 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6113094875102378278727208078196000000000000000000000000 cm36_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 239357414028231496145134456212600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((239357414028231496145134456212600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 239357414028231496145134456212600000000000000000000000000 gm36_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9096981523834313328356865543787400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9096981523834313328356865543787400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9096981523834313328356865543787400000000000000000000000000 gm36_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9096981523834313328356865543787400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9096981523834313328356865543787400000000000000000000000000 * 358490360989006527597059948189 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -4 else if k.val = 2 then 7 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((358490360989006527597059948189 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9096981523834313328356865543787400000000000000000000000000 gm36_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 233244319153129117866407248134404000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb36_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((233244319153129117866407248134404000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((36 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat41.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 233244319153129117866407248134404000000000000000000000000 gm36_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm36_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(36 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (36 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg36 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (36 : Fin 88)),
            if yzBoundary 0 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((36 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((36 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((9732637201921143042050195572629800243385101041855972296024506800000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp36 (fun b ↦
    if yzBoundary 0 (⟨(36 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(36 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(36 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(36 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ36]
  rw [kzero _ gm36_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb36_1_3_0 (add_le_add gb36_0 (add_le_add gb36_1 (add_le_add gb36_2 gb36_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp37 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
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

theorem cm37_2_2_0 :
    ∑ w, mu3 3 1 (⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 6593841078698496010641068378064000000000000000000000000 := by
  decide +kernel

theorem cb37_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((6593841078698496010641068378064000000000000000000000000 * 284538546984324506047673424310 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (37 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((284538546984324506047673424310 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.1 6593841078698496010641068378064000000000000000000000000 cm37_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3632465846499470315488431420590464000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3632465846499470315488431420590464000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.1 3632465846499470315488431420590464000000000000000000000000 gm37_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 12494161721699997388319137158819072000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((12494161721699997388319137158819072000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.1 12494161721699997388319137158819072000000000000000000000000 gm37_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3625872005420771819477790352212400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb37_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3625872005420771819477790352212400000000000000000000000000 * 370868528793585051749516867932 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((37 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 6 else if k.val = 2 then 3 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370868528793585051749516867932 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.1 3625872005420771819477790352212400000000000000000000000000 gm37_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm37_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm37_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(37 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (37 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg37 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (37 : Fin 88)),
            if yzBoundary 0 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((37 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((37 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((10006890989060171156249607394079583027617938132280188054054140320000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp37 (fun b ↦
    if yzBoundary 0 (⟨(37 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(37 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(37 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(37 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(37 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ37]
  rw [kzero _ gm37_3]
  rw [kzero _ gm37_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb37_2_2_0 (add_le_add gb37_0 (add_le_add gb37_1 gb37_2))) (le_of_eq (by push_cast; ring)))

theorem hsp38 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
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

theorem cm38_3_1_0 :
    ∑ w, mu3 3 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 2906556384456333276315627852180000000000000000000000000 := by
  decide +kernel

theorem cb38_3_1_0 :
    ((∑ w, mu3 3 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((2906556384456333276315627852180000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (38 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2906556384456333276315627852180000000000000000000000000 cm38_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4422977698504357944420000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4422977698504357944420000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4422977698504357944420000000000000000000000000000000000000 gm38_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4420071142119901611143684372147820000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb38_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4420071142119901611143684372147820000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((38 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4420071142119901611143684372147820000000000000000000000000 gm38_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm38_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm38_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm38_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(38 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (38 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg38 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (38 : Fin 88)),
            if yzBoundary 0 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((38 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((38 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3065774521397811542819863536772429214084746513277460000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp38 (fun b ↦
    if yzBoundary 0 (⟨(38 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(38 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(38 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(38 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(38 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ38]
  rw [kzero _ gm38_2]
  rw [kzero _ gm38_3]
  rw [kzero _ gm38_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb38_3_1_0 (add_le_add gb38_0 gb38_1)) (le_of_eq (by push_cast; ring)))

theorem hsp39 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
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

theorem gm39_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1299618666696960300788889836773470000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1299618666696960300788889836773470000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1299618666696960300788889836773470000000000000000000000000 gm39_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4510161615688275052380220326453060000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4510161615688275052380220326453060000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4510161615688275052380220326453060000000000000000000000000 gm39_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1299618666696960300788889836773470000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb39_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1299618666696960300788889836773470000000000000000000000000 * 407579647603415688289978436583 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((39 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 8 else if k.val = 2 then -5 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((407579647603415688289978436583 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1299618666696960300788889836773470000000000000000000000000 gm39_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm39_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm39_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(39 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (39 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg39 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (39 : Fin 88)),
            if yzBoundary 0 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((39 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((39 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3655903925975183480688000608102376904684545192183482025527985660000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp39 (fun b ↦
    if yzBoundary 0 (⟨(39 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(39 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(39 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(39 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ39]
  rw [kzero _ gm39_3]
  rw [kzero _ gm39_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb39_0 (add_le_add gb39_1 gb39_2)) (le_of_eq (by push_cast; ring)))

theorem hsp40 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ40 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm40_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3105114235478106512202000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3105114235478106512202000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3105114235478106512202000000000000000000000000000000000000 gm40_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3105114235478106512202000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb40_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3105114235478106512202000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((40 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3105114235478106512202000000000000000000000000000000000000 gm40_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm40_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm40_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm40_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(40 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (40 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg40 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (40 : Fin 88)),
            if yzBoundary 0 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((40 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((40 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2152301177638199632033095131921464459884792450658626000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp40 (fun b ↦
    if yzBoundary 0 (⟨(40 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(40 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(40 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(40 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ40]
  rw [kzero _ gm40_2]
  rw [kzero _ gm40_3]
  rw [kzero _ gm40_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb40_0 gb40_1) (le_of_eq (by push_cast; ring)))

theorem hsp41 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ41 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm41_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 110594666502881652748000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((110594666502881652748000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 110594666502881652748000000000000000000000000000000000000 gm41_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 110594666502881652748000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb41_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((110594666502881652748000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((41 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 110594666502881652748000000000000000000000000000000000000 gm41_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm41_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm41_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm41_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(41 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (41 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg41 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (41 : Fin 88)),
            if yzBoundary 0 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((41 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((41 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76658381271439844230867211568844110417543745485724000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp41 (fun b ↦
    if yzBoundary 0 (⟨(41 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(41 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(41 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(41 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ41]
  rw [kzero _ gm41_2]
  rw [kzero _ gm41_3]
  rw [kzero _ gm41_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb41_0 gb41_1) (le_of_eq (by push_cast; ring)))

theorem hsp42 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ42 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm42_0_4_0 :
    ∑ w, mu3 3 1 (⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 25813787892074082369393696997794000000000000000000000000 := by
  decide +kernel

theorem cb42_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((25813787892074082369393696997794000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25813787892074082369393696997794000000000000000000000000 cm42_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm42_1_3_0 :
    ∑ w, mu3 3 1 (⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 84456807258043742433606303002206000000000000000000000000 := by
  decide +kernel

theorem cb42_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((84456807258043742433606303002206000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (42 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84456807258043742433606303002206000000000000000000000000 cm42_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm42_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm42_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25813787892074082369393696997794000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25813787892074082369393696997794000000000000000000000000 * 179530218624328578977802995314 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 1 else if k.val = 2 then 0 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((179530218624328578977802995314 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25813787892074082369393696997794000000000000000000000000 gm42_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84456807258043742433606303002206000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb42_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84456807258043742433606303002206000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((42 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84456807258043742433606303002206000000000000000000000000 gm42_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm42_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(42 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (42 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg42 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (42 : Fin 88)),
            if yzBoundary 0 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((42 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((42 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((121716350643801596906615154011446983580607205709622965961348346000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp42 (fun b ↦
    if yzBoundary 0 (⟨(42 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(42 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(42 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(42 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(42 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(42 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ42]
  rw [kzero _ gm42_0]
  rw [kzero _ gm42_1]
  rw [kzero _ gm42_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb42_0_4_0 (add_le_add cb42_1_3_0 (add_le_add gb42_2 gb42_3))) (le_of_eq (by push_cast; ring)))

theorem hsp43 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
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

theorem cm43_0_4_0 :
    ∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 28882717060203756244353168491280000000000000000000000000 := by
  decide +kernel

theorem cb43_0_4_0 :
    ((∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((28882717060203756244353168491280000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28882717060203756244353168491280000000000000000000000000 cm43_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm43_1_3_0 :
    ∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 1304850802282796131784484266808960000000000000000000000000 := by
  decide +kernel

theorem cb43_1_3_0 :
    ((∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((1304850802282796131784484266808960000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1304850802282796131784484266808960000000000000000000000000 cm43_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm43_2_2_0 :
    ∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w = 718742100900656116019162564699760000000000000000000000000 := by
  decide +kernel

theorem cb43_2_2_0 :
    ((∑ w, mu3 3 1 (⟨(43 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 (⟨(43 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3))) w : ℚ) : ℝ)) ≤
      ((718742100900656116019162564699760000000000000000000000000 * 412615101178124675464119326450 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (43 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-14 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((412615101178124675464119326450 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 718742100900656116019162564699760000000000000000000000000 cm43_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 3 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm43_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 28882717060203756244353168491280000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 3 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((28882717060203756244353168491280000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28882717060203756244353168491280000000000000000000000000 gm43_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1304850802282796131784484266808960000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 3 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1304850802282796131784484266808960000000000000000000000000 * 147382074205329146269614891 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 4 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((147382074205329146269614891 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1304850802282796131784484266808960000000000000000000000000 gm43_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 718742100900656116019162564699760000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 3 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb43_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((718742100900656116019162564699760000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((43 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat42.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 718742100900656116019162564699760000000000000000000000000 gm43_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm43_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 3 1 ⟨(43 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (43 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg43 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 (43 : Fin 88)),
            if yzBoundary 0 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr ((43 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr ((43 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1719423845641786212417107642072280380852184208980540702524314320000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp43 (fun b ↦
    if yzBoundary 0 (⟨(43 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
      ((∑ w, mu3 3 1 ⟨(43 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 3 1 ⟨(43 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(43 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(43 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(43 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(43 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) from rfl)]
  rw [hJ43]
  rw [kzero _ gm43_0]
  rw [kzero _ gm43_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb43_0_4_0 (add_le_add cb43_1_3_0 (add_le_add cb43_2_2_0 (add_le_add gb43_1 (add_le_add gb43_2 gb43_3))))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88), (22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((357226043044211383603631705308351906863713459835088551792670676942000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg0 (add_le_add L3K.reg1 (add_le_add L3K.reg2 (add_le_add L3K.reg3 (add_le_add L3K.reg4 (add_le_add L3K.reg5 (add_le_add L3K.reg6 (add_le_add L3K.reg7 (add_le_add L3K.reg8 (add_le_add L3K.reg9 (add_le_add L3K.reg10 (add_le_add L3K.reg11 (add_le_add L3K.reg12 (add_le_add L3K.reg13 (add_le_add L3K.reg14 (add_le_add L3K.reg15 (add_le_add L3K.reg16 (add_le_add L3K.reg17 (add_le_add L3K.reg18 (add_le_add L3K.reg19 (add_le_add L3K.reg20 (add_le_add L3K.reg21 (add_le_add L3K.reg22 (add_le_add L3K.reg23 (add_le_add L3K.reg24 (add_le_add L3K.reg25 (add_le_add L3K.reg26 (add_le_add L3K.reg27 (add_le_add L3K.reg28 (add_le_add L3K.reg29 (add_le_add L3K.reg30 (add_le_add L3K.reg31 (add_le_add L3K.reg32 (add_le_add L3K.reg33 (add_le_add L3K.reg34 (add_le_add L3K.reg35 (add_le_add L3K.reg36 (add_le_add L3K.reg37 (add_le_add L3K.reg38 (add_le_add L3K.reg39 (add_le_add L3K.reg40 (add_le_add L3K.reg41 (add_le_add L3K.reg42 L3K.reg43))))))))))))))))))))))))))))))))))))))))))) (le_of_eq (by push_cast; ring))
