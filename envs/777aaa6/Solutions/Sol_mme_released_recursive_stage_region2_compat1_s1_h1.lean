-- Prove2me | solution 1 for mme_released_recursive_stage_region2_compat1_s1_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T14:36:20.042513+00:00
-- url     : https://prove2.me/submissions/dc51d0b7-82a8-4505-9ee1-0b0aaba7f2cb

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_released_recursive_level3_compat33
import Theorems.Thm_mme_released_recursive_level3_compat34
import Theorems.Thm_mme_released_recursive_level3_compat35
import Theorems.Thm_mme_released_recursive_level3_compat36
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

theorem hcell (f : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2) → ℕ) :
    ∑ c, f c = ∑ a : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 a), f ⟨a, b⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem hgrp1 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 rr),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = jj.val then mu3 2 1 ⟨rr, c⟩ w else 0 := by
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



noncomputable abbrev MU := partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)

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

theorem kstepC (a : Fin 88) (b : Split (2 * 2 ^ (2 - 1)) (parent3 2 a))
    (hb : yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 2 1 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 2 1 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
      ((mass : ℕ) : ℝ) * ((q : ℚ) : ℝ) := by
  rw [hm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact le_trans (mme_certified_potential_ceiling.{0, 0}.1
    (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) (freq_nonneg _) e) (by exact_mod_cast h)

theorem hsp66 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ66 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm66_2_2_0 :
    ∑ w, mu3 2 1 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 549995053065520903236028835974660000000000000000000000000 := by
  decide +kernel

theorem cb66_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((549995053065520903236028835974660000000000000000000000000 * 398424377997923643848471971000 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398424377997923643848471971000 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 549995053065520903236028835974660000000000000000000000000 cm66_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_3_1_0 :
    ∑ w, mu3 2 1 (⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 74405241811723551768439969281056000000000000000000000000 := by
  decide +kernel

theorem cb66_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((74405241811723551768439969281056000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 74405241811723551768439969281056000000000000000000000000 cm66_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8372238380482407182619253107642408000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (66 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8372238380482407182619253107642408000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8372238380482407182619253107642408000000000000000000000000 gm66_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 28521234142595405208697053815434128000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (66 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((28521234142595405208697053815434128000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 28521234142595405208697053815434128000000000000000000000000 gm66_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7822243327416886279383224271667748000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (66 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7822243327416886279383224271667748000000000000000000000000 * 207720996794988825491575738308 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then 2 else if k.val = 2 then 2 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207720996794988825491575738308 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7822243327416886279383224271667748000000000000000000000000 gm66_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (66 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm66_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (66 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg66 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
            if yzBoundary 0 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((66 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((66 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((21664962433674282349549770163068426284408153403680408366160338344000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp66 (fun b ↦
    if yzBoundary 0 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(66 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ66]
  rw [kzero _ gm66_3]
  rw [kzero _ gm66_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb66_2_2_0 (add_le_add cb66_3_1_0 (add_le_add gb66_0 (add_le_add gb66_1 gb66_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp67 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ67 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm67_1_3_0 :
    ∑ w, mu3 2 1 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6993995270709043528801972218468000000000000000000000000 := by
  decide +kernel

theorem cb67_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6993995270709043528801972218468000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6993995270709043528801972218468000000000000000000000000 cm67_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 277623166254814351653949458453020000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (67 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((277623166254814351653949458453020000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 277623166254814351653949458453020000000000000000000000000 gm67_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10319993478924455643382050541546980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (67 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10319993478924455643382050541546980000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10319993478924455643382050541546980000000000000000000000000 gm67_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10319993478924455643382050541546980000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (67 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10319993478924455643382050541546980000000000000000000000000 * 361617033405388144590118377641 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361617033405388144590118377641 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10319993478924455643382050541546980000000000000000000000000 gm67_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 270629170984105308125147486234552000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (67 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((270629170984105308125147486234552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 270629170984105308125147486234552000000000000000000000000 gm67_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (67 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg67 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
            if yzBoundary 0 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((67 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((67 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((11077593524872770012491171682848309685531662343354482950192245320000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp67 (fun b ↦
    if yzBoundary 0 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(67 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ67]
  rw [kzero _ gm67_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb67_1_3_0 (add_le_add gb67_0 (add_le_add gb67_1 (add_le_add gb67_2 gb67_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp68 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ68 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm68_1_3_0 :
    ∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 718843348779305789483012687580504000000000000000000000000 := by
  decide +kernel

theorem cb68_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((718843348779305789483012687580504000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.1 718843348779305789483012687580504000000000000000000000000 cm68_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_2_2_0 :
    ∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 10183751779023220197432558195692280000000000000000000000000 := by
  decide +kernel

theorem cb68_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((10183751779023220197432558195692280000000000000000000000000 * 403054958646898951419494023956 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (31 : Int) else if k.val = 1 then -4 else if k.val = 2 then -4 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403054958646898951419494023956 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.1 10183751779023220197432558195692280000000000000000000000000 cm68_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_3_1_0 :
    ∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 668242182960679888598645363219280000000000000000000000000 := by
  decide +kernel

theorem cb68_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((668242182960679888598645363219280000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.1 668242182960679888598645363219280000000000000000000000000 cm68_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 812548164320052220406068261198056000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (68 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((812548164320052220406068261198056000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.1 812548164320052220406068261198056000000000000000000000000 gm68_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29671917002306594796907286375582664000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (68 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29671917002306594796907286375582664000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.1 29671917002306594796907286375582664000000000000000000000000 gm68_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 20156407406244054488073373543109664000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (68 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((20156407406244054488073373543109664000000000000000000000000 * 96887093759473836969963751449 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((96887093759473836969963751449 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.1 20156407406244054488073373543109664000000000000000000000000 gm68_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 93704815540746430923055573617552000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (68 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((93704815540746430923055573617552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.1 93704815540746430923055573617552000000000000000000000000 gm68_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (68 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg68 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
            if yzBoundary 0 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((68 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((68 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((27650918652562950369920671166307846470652985608209554538798549208000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp68 (fun b ↦
    if yzBoundary 0 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ68]
  rw [kzero _ gm68_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb68_1_3_0 (add_le_add cb68_2_2_0 (add_le_add cb68_3_1_0 (add_le_add gb68_0 (add_le_add gb68_1 (add_le_add gb68_2 gb68_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp69 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ69 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm69_0_4_0 :
    ∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4641148990723088437724181837240000000000000000000000000 := by
  decide +kernel

theorem cb69_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4641148990723088437724181837240000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4641148990723088437724181837240000000000000000000000000 cm69_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_1_3_0 :
    ∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 568618652676452326481588833661520000000000000000000000000 := by
  decide +kernel

theorem cb69_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(69 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((568618652676452326481588833661520000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 568618652676452326481588833661520000000000000000000000000 cm69_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_2_2_0 :
    ∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 2037727006025249471743123008646860000000000000000000000000 := by
  decide +kernel

theorem cb69_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((2037727006025249471743123008646860000000000000000000000000 * 374844765975040782052359999197 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -1 else if k.val = 2 then 4 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((374844765975040782052359999197 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2037727006025249471743123008646860000000000000000000000000 cm69_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4641148990723088437724181837240000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (69 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4641148990723088437724181837240000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4641148990723088437724181837240000000000000000000000000 gm69_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1075473840730785663337232866145160000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (69 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1075473840730785663337232866145160000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1075473840730785663337232866145160000000000000000000000000 gm69_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9918196500740286051226962895388340000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (69 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9918196500740286051226962895388340000000000000000000000000 * 202629568714638051036300293516 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (28 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((202629568714638051036300293516 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9918196500740286051226962895388340000000000000000000000000 gm69_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 506855188054333336855644032483640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (69 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((506855188054333336855644032483640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 506855188054333336855644032483640000000000000000000000000 gm69_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (69 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg69 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
            if yzBoundary 0 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((69 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((69 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4264474503003631124196179494493312343947242704116461775960038140000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp69 (fun b ↦
    if yzBoundary 0 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(69 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(69 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ69]
  rw [kzero _ gm69_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb69_0_4_0 (add_le_add cb69_1_3_0 (add_le_add cb69_2_2_0 (add_le_add gb69_0 (add_le_add gb69_1 (add_le_add gb69_2 gb69_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp70 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ70 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm70_0_4_0 :
    ∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 21309305200459256409010112555525000000000000000000000000 := by
  decide +kernel

theorem cb70_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((21309305200459256409010112555525000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21309305200459256409010112555525000000000000000000000000 cm70_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_1_3_0 :
    ∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4119394465355683516197180657373822000000000000000000000000 := by
  decide +kernel

theorem cb70_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4119394465355683516197180657373822000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4119394465355683516197180657373822000000000000000000000000 cm70_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_2_2_0 :
    ∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 27939431328980017165700358874039691000000000000000000000000 := by
  decide +kernel

theorem cb70_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((27939431328980017165700358874039691000000000000000000000000 * 377351695753138882148719425352 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-28 : Int) else if k.val = 1 then -3 else if k.val = 2 then 8 else 5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then 3 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((377351695753138882148719425352 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 27939431328980017165700358874039691000000000000000000000000 cm70_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_3_1_0 :
    ∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 804875533400573679692450356030962000000000000000000000000 := by
  decide +kernel

theorem cb70_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((804875533400573679692450356030962000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 804875533400573679692450356030962000000000000000000000000 cm70_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21309305200459256409010112555525000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (70 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21309305200459256409010112555525000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21309305200459256409010112555525000000000000000000000000 gm70_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4119394465355683516197180657373822000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (70 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4119394465355683516197180657373822000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4119394465355683516197180657373822000000000000000000000000 gm70_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 27939431328980017165700358874039691000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (70 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((27939431328980017165700358874039691000000000000000000000000 * 18673657391087924324339337876 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 8 else if k.val = 2 then 6 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((18673657391087924324339337876 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 27939431328980017165700358874039691000000000000000000000000 gm70_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 804875533400573679692450356030962000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (70 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((804875533400573679692450356030962000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 804875533400573679692450356030962000000000000000000000000 gm70_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (70 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg70 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
            if yzBoundary 0 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((70 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((70 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17891210890615835524831010706410760871970053848634667059723917306000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp70 (fun b ↦
    if yzBoundary 0 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(70 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(70 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ70]
  rw [kzero _ gm70_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb70_0_4_0 (add_le_add cb70_1_3_0 (add_le_add cb70_2_2_0 (add_le_add cb70_3_1_0 (add_le_add gb70_0 (add_le_add gb70_1 (add_le_add gb70_2 gb70_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp71 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ71 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm71_0_4_0 :
    ∑ w, mu3 2 1 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 7707852404896207898412334769800000000000000000000000000 := by
  decide +kernel

theorem cb71_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((7707852404896207898412334769800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7707852404896207898412334769800000000000000000000000000 cm71_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm71_1_3_0 :
    ∑ w, mu3 2 1 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 189379990614143106552908278024320000000000000000000000000 := by
  decide +kernel

theorem cb71_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((189379990614143106552908278024320000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 189379990614143106552908278024320000000000000000000000000 cm71_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (71 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm71_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7707852404896207898412334769800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (71 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7707852404896207898412334769800000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7707852404896207898412334769800000000000000000000000000 gm71_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 530746915309406224381587665230200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (71 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((530746915309406224381587665230200000000000000000000000000 * 227705816079512444920321792382 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (21 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((227705816079512444920321792382 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 530746915309406224381587665230200000000000000000000000000 gm71_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 341366924695263117828679387205880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (71 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((341366924695263117828679387205880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 341366924695263117828679387205880000000000000000000000000 gm71_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (71 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg71 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
            if yzBoundary 0 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((71 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((71 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((494082563582441219785450739838442640053518382241289130979725000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp71 (fun b ↦
    if yzBoundary 0 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(71 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(71 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ71]
  rw [kzero _ gm71_0]
  rw [kzero _ gm71_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb71_0_4_0 (add_le_add cb71_1_3_0 (add_le_add gb71_1 (add_le_add gb71_2 gb71_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp72 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ72 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm72_0_4_0 :
    ∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 29115794560556955198381523109096000000000000000000000000 := by
  decide +kernel

theorem cb72_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((29115794560556955198381523109096000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29115794560556955198381523109096000000000000000000000000 cm72_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_1_3_0 :
    ∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1314472634936095997998731450658976000000000000000000000000 := by
  decide +kernel

theorem cb72_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(72 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1314472634936095997998731450658976000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1314472634936095997998731450658976000000000000000000000000 cm72_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_2_2_0 :
    ∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 724461817410532619326887026231928000000000000000000000000 := by
  decide +kernel

theorem cb72_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((724461817410532619326887026231928000000000000000000000000 * 412444510880769565304413315075 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -2 else if k.val = 2 then -2 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -8 else if k.val = 2 then 7 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((412444510880769565304413315075 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 724461817410532619326887026231928000000000000000000000000 cm72_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (72 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm72_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 29115794560556955198381523109096000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (72 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((29115794560556955198381523109096000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29115794560556955198381523109096000000000000000000000000 gm72_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1314472634936095997998731450658976000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (72 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1314472634936095997998731450658976000000000000000000000000 * 151642608914746286992461636 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((151642608914746286992461636 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1314472634936095997998731450658976000000000000000000000000 gm72_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 724461817410532619326887026231928000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (72 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((724461817410532619326887026231928000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 724461817410532619326887026231928000000000000000000000000 gm72_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (72 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg72 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
            if yzBoundary 0 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((72 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((72 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1732462827893403702216775606854492378080790584818131155549523008000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp72 (fun b ↦
    if yzBoundary 0 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(72 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(72 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(72 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(72 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ72]
  rw [kzero _ gm72_0]
  rw [kzero _ gm72_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb72_0_4_0 (add_le_add cb72_1_3_0 (add_le_add cb72_2_2_0 (add_le_add gb72_1 (add_le_add gb72_2 gb72_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp73 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ73 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm73_0_4_0 :
    ∑ w, mu3 2 1 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25767992860467236471185563168192000000000000000000000000 := by
  decide +kernel

theorem cb73_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25767992860467236471185563168192000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25767992860467236471185563168192000000000000000000000000 cm73_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm73_1_3_0 :
    ∑ w, mu3 2 1 (⟨(73 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84537062021935542576814436831808000000000000000000000000 := by
  decide +kernel

theorem cb73_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(73 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(73 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84537062021935542576814436831808000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84537062021935542576814436831808000000000000000000000000 cm73_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (73 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm73_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (73 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm73_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25767992860467236471185563168192000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (73 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25767992860467236471185563168192000000000000000000000000 * 179834958697514749342137891858 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (3 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((179834958697514749342137891858 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25767992860467236471185563168192000000000000000000000000 gm73_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84537062021935542576814436831808000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (73 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84537062021935542576814436831808000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84537062021935542576814436831808000000000000000000000000 gm73_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (73 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg73 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
            if yzBoundary 0 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((73 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((73 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((121827238318431682072261276064590070820717643596953269073539776000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp73 (fun b ↦
    if yzBoundary 0 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(73 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(73 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(73 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ73]
  rw [kzero _ gm73_0]
  rw [kzero _ gm73_1]
  rw [kzero _ gm73_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb73_0_4_0 (add_le_add cb73_1_3_0 (add_le_add gb73_2 gb73_3))) (le_of_eq (by push_cast; ring)))

theorem hsp74 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩)} := by
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

theorem gm74_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111445588322840301966000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (74 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb74_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111445588322840301966000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111445588322840301966000000000000000000000000000000000000 gm74_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 111445588322840301966000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (74 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb74_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((111445588322840301966000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 111445588322840301966000000000000000000000000000000000000 gm74_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (74 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (74 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (74 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg74 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
            if yzBoundary 0 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((74 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((74 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((77248195331821119334699737676157597852377001925558000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp74 (fun b ↦
    if yzBoundary 0 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(74 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(74 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(74 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(74 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ74]
  rw [kzero _ gm74_2]
  rw [kzero _ gm74_3]
  rw [kzero _ gm74_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb74_0 gb74_1) (le_of_eq (by push_cast; ring)))

theorem hsp75 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ75 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm75_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2821845899840507345252000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (75 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb75_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2821845899840507345252000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.1 2821845899840507345252000000000000000000000000000000000000 gm75_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2821845899840507345252000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (75 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb75_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2821845899840507345252000000000000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.1 2821845899840507345252000000000000000000000000000000000000 gm75_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (75 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (75 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (75 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg75 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
            if yzBoundary 0 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((75 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((75 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1955954529449089491644653355878739220747454311488276000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp75 (fun b ↦
    if yzBoundary 0 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(75 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ75]
  rw [kzero _ gm75_2]
  rw [kzero _ gm75_3]
  rw [kzero _ gm75_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb75_0 gb75_1) (le_of_eq (by push_cast; ring)))

theorem hsp76 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ76 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm76_3_1_0 :
    ∑ w, mu3 2 1 (⟨(76 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 3895259040618605539168576104216000000000000000000000000 := by
  decide +kernel

theorem cb76_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(76 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(76 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((3895259040618605539168576104216000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.1 3895259040618605539168576104216000000000000000000000000 cm76_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5926568303523453246126000000000000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (76 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5926568303523453246126000000000000000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.1 5926568303523453246126000000000000000000000000000000000000 gm76_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 5922673044482834640586831423895784000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (76 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((5922673044482834640586831423895784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.1 5922673044482834640586831423895784000000000000000000000000 gm76_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (76 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm76_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (76 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm76_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (76 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg76 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
            if yzBoundary 0 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((76 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((76 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((4107984109983219803912888514390122479120694250199638000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp76 (fun b ↦
    if yzBoundary 0 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(76 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(76 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ76]
  rw [kzero _ gm76_2]
  rw [kzero _ gm76_3]
  rw [kzero _ gm76_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb76_3_1_0 (add_le_add gb76_0 gb76_1)) (le_of_eq (by push_cast; ring)))

theorem hsp77 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)))) = {(⟨![1,1,2], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ77 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm77_3_1_0 :
    ∑ w, mu3 2 1 (⟨(77 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 149577046232736840793649670877938000000000000000000000000 := by
  decide +kernel

theorem cb77_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(77 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(77 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((149577046232736840793649670877938000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 149577046232736840793649670877938000000000000000000000000 cm77_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_4_0_0 :
    ∑ w, mu3 2 1 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6087774109725946354519405263024000000000000000000000000 := by
  decide +kernel

theorem cb77_4_0_0 :
    ((∑ w, mu3 2 1 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6087774109725946354519405263024000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6087774109725946354519405263024000000000000000000000000 cm77_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 419312041248915101443480594736976000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (77 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((419312041248915101443480594736976000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 419312041248915101443480594736976000000000000000000000000 gm77_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 275822769125904207004350329122062000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (77 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((275822769125904207004350329122062000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 275822769125904207004350329122062000000000000000000000000 gm77_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (77 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm77_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (77 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm77_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (77 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg77 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
            if yzBoundary 0 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((77 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((77 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((294864682626563362150456958136396957477565267621374000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp77 (fun b ↦
    if yzBoundary 0 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(77 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(77 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(77 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(77 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ77]
  rw [kzero _ gm77_2]
  rw [kzero _ gm77_3]
  rw [kzero _ gm77_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb77_3_1_0 (add_le_add cb77_4_0_0 (add_le_add gb77_0 gb77_1))) (le_of_eq (by push_cast; ring)))

theorem hsp78 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)))) = {(⟨![2,1,1], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ78 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm78_3_1_0 :
    ∑ w, mu3 2 1 (⟨(78 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84448430638772369604075266185084000000000000000000000000 := by
  decide +kernel

theorem cb78_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(78 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(78 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84448430638772369604075266185084000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84448430638772369604075266185084000000000000000000000000 cm78_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm78_4_0_0 :
    ∑ w, mu3 2 1 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25796342675231138911924733814916000000000000000000000000 := by
  decide +kernel

theorem cb78_4_0_0 :
    ((∑ w, mu3 2 1 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25796342675231138911924733814916000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25796342675231138911924733814916000000000000000000000000 cm78_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84448430638772369604075266185084000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (78 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84448430638772369604075266185084000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84448430638772369604075266185084000000000000000000000000 gm78_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25796342675231138911924733814916000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (78 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25796342675231138911924733814916000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25796342675231138911924733814916000000000000000000000000 gm78_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (78 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm78_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (78 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm78_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (78 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg78 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
            if yzBoundary 0 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((78 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((78 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76415853794071830142913790988630559365738273610708000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp78 (fun b ↦
    if yzBoundary 0 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(78 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(78 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(78 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ78]
  rw [kzero _ gm78_2]
  rw [kzero _ gm78_3]
  rw [kzero _ gm78_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb78_3_1_0 (add_le_add cb78_4_0_0 (add_le_add gb78_0 gb78_1))) (le_of_eq (by push_cast; ring)))

theorem hsp79 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ79 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem gm79_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1191799770630583974397392368815400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (79 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1191799770630583974397392368815400000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1191799770630583974397392368815400000000000000000000000000 gm79_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4069993291526853634505215262369200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (79 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4069993291526853634505215262369200000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4069993291526853634505215262369200000000000000000000000000 gm79_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1191799770630583974397392368815400000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (79 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1191799770630583974397392368815400000000000000000000000000 * 424526343910964590202019997946 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 2 else if k.val = 2 then -8 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424526343910964590202019997946 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1191799770630583974397392368815400000000000000000000000000 gm79_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (79 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm79_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (79 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg79 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
            if yzBoundary 0 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((79 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((79 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3327054774219458152240789275592987087725718824896544644209091400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp79 (fun b ↦
    if yzBoundary 0 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ79]
  rw [kzero _ gm79_3]
  rw [kzero _ gm79_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add gb79_0 (add_le_add gb79_1 gb79_2)) (le_of_eq (by push_cast; ring)))

theorem hsp80 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)))) = {(⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ80 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm80_2_2_0 :
    ∑ w, mu3 2 1 (⟨(80 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 631414952879840861408084858912000000000000000000000000000 := by
  decide +kernel

theorem cb80_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(80 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(80 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((631414952879840861408084858912000000000000000000000000000 * 398997108138342041426178179154 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -2 else if k.val = 2 then -1 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((398997108138342041426178179154 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 631414952879840861408084858912000000000000000000000000000 cm80_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_3_1_0 :
    ∑ w, mu3 2 1 (⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 85878687665783984425604424681600000000000000000000000000 := by
  decide +kernel

theorem cb80_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((85878687665783984425604424681600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85878687665783984425604424681600000000000000000000000000 cm80_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 9617172793880429871791906607555200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (80 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((9617172793880429871791906607555200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 9617172793880429871791906607555200000000000000000000000000 gm80_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32743685919532441590390582360208000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (80 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32743685919532441590390582360208000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32743685919532441590390582360208000000000000000000000000000 gm80_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8985757841000589010383821748643200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (80 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8985757841000589010383821748643200000000000000000000000000 * 207631744058296756016362179190 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -6 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (20 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((207631744058296756016362179190 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8985757841000589010383821748643200000000000000000000000000 gm80_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (80 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm80_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (80 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg80 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
            if yzBoundary 0 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((80 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((80 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((24873381458936850012700988348419831472752016442942635271057680000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp80 (fun b ↦
    if yzBoundary 0 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(80 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ80]
  rw [kzero _ gm80_3]
  rw [kzero _ gm80_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb80_2_2_0 (add_le_add cb80_3_1_0 (add_le_add gb80_0 (add_le_add gb80_1 gb80_2)))) (le_of_eq (by push_cast; ring)))

theorem hsp81 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) + g (⟨![4,0,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩), (⟨![4,0,0], by decide +kernel⟩)} := by
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

theorem cm81_2_2_0 :
    ∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 5336919835023709980018128280938412000000000000000000000000 := by
  decide +kernel

theorem cb81_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((5336919835023709980018128280938412000000000000000000000000 * 333748470512302533450920709132 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then 8 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (25 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((333748470512302533450920709132 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5336919835023709980018128280938412000000000000000000000000 cm81_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_3_1_0 :
    ∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1469761010792973363093471483324788000000000000000000000000 := by
  decide +kernel

theorem cb81_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1469761010792973363093471483324788000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1469761010792973363093471483324788000000000000000000000000 cm81_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_4_0_0 :
    ∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 12142251382117114678981186724904000000000000000000000000 := by
  decide +kernel

theorem cb81_4_0_0 :
    ((∑ w, mu3 2 1 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((12142251382117114678981186724904000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12142251382117114678981186724904000000000000000000000000 cm81_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6707147516659869507370778183316977000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (81 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6707147516659869507370778183316977000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6707147516659869507370778183316977000000000000000000000000 gm81_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22071933002674231682549009776591450000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (81 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22071933002674231682549009776591450000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 22071933002674231682549009776591450000000000000000000000000 gm81_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1382369933018276642031631089103469000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (81 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1382369933018276642031631089103469000000000000000000000000 * 4772518915768318131921581 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -6 else if k.val = 2 then 5 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((4772518915768318131921581 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1382369933018276642031631089103469000000000000000000000000 gm81_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (81 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm81_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (81 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg81 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
            if yzBoundary 0 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((81 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((81 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((18099054260612323429415669742915557397453039678187444213564833468000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp81 (fun b ↦
    if yzBoundary 0 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_pos (show yzBoundary 0 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ81]
  rw [kzero _ gm81_3]
  rw [kzero _ gm81_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb81_2_2_0 (add_le_add cb81_3_1_0 (add_le_add cb81_4_0_0 (add_le_add gb81_0 (add_le_add gb81_1 gb81_2))))) (le_of_eq (by push_cast; ring)))

theorem hsp82 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,0,4], by decide +kernel⟩) + g (⟨![0,1,3], by decide +kernel⟩) + g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,0,3], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)))) = {(⟨![0,0,4], by decide +kernel⟩), (⟨![0,1,3], by decide +kernel⟩), (⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,0,3], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ82 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm82_1_3_0 :
    ∑ w, mu3 2 1 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6982514479028264223519614939638000000000000000000000000 := by
  decide +kernel

theorem cb82_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6982514479028264223519614939638000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6982514479028264223519614939638000000000000000000000000 cm82_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 277132341605868300747775949721454000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (82 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((277132341605868300747775949721454000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 277132341605868300747775949721454000000000000000000000000 gm82_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10347986367548502758070224050278546000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (82 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10347986367548502758070224050278546000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10347986367548502758070224050278546000000000000000000000000 gm82_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10347986367548502758070224050278546000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (82 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10347986367548502758070224050278546000000000000000000000000 * 361197095939108290121799281834 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((361197095939108290121799281834 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10347986367548502758070224050278546000000000000000000000000 gm82_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 270149827126840036524256334781816000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (82 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((270149827126840036524256334781816000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 270149827126840036524256334781816000000000000000000000000 gm82_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (82 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg82 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
            if yzBoundary 0 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((82 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((82 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((11102433701141079118932202377059585086284728793267884042105783542000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp82 (fun b ↦
    if yzBoundary 0 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ82]
  rw [kzero _ gm82_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb82_1_3_0 (add_le_add gb82_0 (add_le_add gb82_1 (add_le_add gb82_2 gb82_3)))) (le_of_eq (by push_cast; ring)))

theorem hsp83 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ83 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm83_1_3_0 :
    ∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 810491575813781471082071704028352000000000000000000000000 := by
  decide +kernel

theorem cb83_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(83 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((810491575813781471082071704028352000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.1 810491575813781471082071704028352000000000000000000000000 cm83_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_2_2_0 :
    ∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 11567588782490306859751896857719872000000000000000000000000 := by
  decide +kernel

theorem cb83_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((11567588782490306859751896857719872000000000000000000000000 * 403518790679032176895820998136 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((403518790679032176895820998136 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.1 11567588782490306859751896857719872000000000000000000000000 cm83_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_3_1_0 :
    ∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 763180712521234715272414333598400000000000000000000000000 := by
  decide +kernel

theorem cb83_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((763180712521234715272414333598400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.1 763180712521234715272414333598400000000000000000000000000 cm83_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 916751921467789531544600041722432000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (83 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((916751921467789531544600041722432000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.1 916751921467789531544600041722432000000000000000000000000 gm83_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33697445178596354224798985624679168000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (83 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33697445178596354224798985624679168000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.1 33697445178596354224798985624679168000000000000000000000000 gm83_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 22893037108627282080319503100557696000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (83 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((22893037108627282080319503100557696000000000000000000000000 * 95709857963440136914412633412 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 3 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((95709857963440136914412633412 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.1 22893037108627282080319503100557696000000000000000000000000 gm83_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 106260345654008060462528337694080000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (83 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((106260345654008060462528337694080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.1 106260345654008060462528337694080000000000000000000000000 gm83_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (83 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg83 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
            if yzBoundary 0 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((83 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((83 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((31380558452998828606186311498559661544701699255164835757617554368000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp83 (fun b ↦
    if yzBoundary 0 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(83 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ83]
  rw [kzero _ gm83_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb83_1_3_0 (add_le_add cb83_2_2_0 (add_le_add cb83_3_1_0 (add_le_add gb83_0 (add_le_add gb83_1 (add_le_add gb83_2 gb83_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp84 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,2,2], by decide +kernel⟩) + g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,1,2], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,0,2], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)))) = {(⟨![0,2,2], by decide +kernel⟩), (⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,1,2], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,0,2], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ84 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm84_0_4_0 :
    ∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 360962513921752762264364771520000000000000000000000000 := by
  decide +kernel

theorem cb84_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((360962513921752762264364771520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360962513921752762264364771520000000000000000000000000 cm84_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_1_3_0 :
    ∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 42682400008043575834840767913184000000000000000000000000 := by
  decide +kernel

theorem cb84_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((42682400008043575834840767913184000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 42682400008043575834840767913184000000000000000000000000 cm84_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_2_2_0 :
    ∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 165382910392113540431910847930512000000000000000000000000 := by
  decide +kernel

theorem cb84_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((165382910392113540431910847930512000000000000000000000000 * 370434443358720428313781441630 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -1 else if k.val = 2 then 7 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((370434443358720428313781441630 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 165382910392113540431910847930512000000000000000000000000 cm84_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 360962513921752762264364771520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (84 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((360962513921752762264364771520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360962513921752762264364771520000000000000000000000000 gm84_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 81217166633382281775689199585120000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (84 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((81217166633382281775689199585120000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 81217166633382281775689199585120000000000000000000000000 gm84_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 803065670112133997436182023356208000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (84 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((803065670112133997436182023356208000000000000000000000000 * 188346341177968591177884449166 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -5) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -5 else 8) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -5) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((188346341177968591177884449166 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 803065670112133997436182023356208000000000000000000000000 gm84_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 38534766625338705940848431671936000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (84 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((38534766625338705940848431671936000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38534766625338705940848431671936000000000000000000000000 gm84_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (84 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg84 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
            if yzBoundary 0 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((84 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((84 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((325108907173394071396889188117649193731071917889302881532359808000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp84 (fun b ↦
    if yzBoundary 0 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ84]
  rw [kzero _ gm84_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb84_0_4_0 (add_le_add cb84_1_3_0 (add_le_add cb84_2_2_0 (add_le_add gb84_0 (add_le_add gb84_1 (add_le_add gb84_2 gb84_3)))))) (le_of_eq (by push_cast; ring)))

theorem hsp85 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) + g (⟨![3,0,1], by decide +kernel⟩) + g (⟨![3,1,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩), (⟨![3,0,1], by decide +kernel⟩), (⟨![3,1,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ85 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm85_0_4_0 :
    ∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25343893829624423990405482978108000000000000000000000000 := by
  decide +kernel

theorem cb85_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25343893829624423990405482978108000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25343893829624423990405482978108000000000000000000000000 cm85_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_1_3_0 :
    ∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4551662161028805409475115639655380000000000000000000000000 := by
  decide +kernel

theorem cb85_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4551662161028805409475115639655380000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4551662161028805409475115639655380000000000000000000000000 cm85_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_2_2_0 :
    ∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 33385342670676514356684755002854260000000000000000000000000 := by
  decide +kernel

theorem cb85_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((33385342670676514356684755002854260000000000000000000000000 * 368644130466246328270572211378 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 7 else if k.val = 2 then 2 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((368644130466246328270572211378 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33385342670676514356684755002854260000000000000000000000000 cm85_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_3_1_0 :
    ∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 942420854827884418093723874512252000000000000000000000000 := by
  decide +kernel

theorem cb85_3_1_0 :
    ((∑ w, mu3 2 1 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((942420854827884418093723874512252000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![3,1,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 942420854827884418093723874512252000000000000000000000000 cm85_3_1_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25343893829624423990405482978108000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (85 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_0 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25343893829624423990405482978108000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25343893829624423990405482978108000000000000000000000000 gm85_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4551662161028805409475115639655380000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (85 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4551662161028805409475115639655380000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4551662161028805409475115639655380000000000000000000000000 gm85_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 33385342670676514356684755002854260000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (85 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((33385342670676514356684755002854260000000000000000000000000 * 10583316449655639000262452047 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then -1 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((10583316449655639000262452047 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 33385342670676514356684755002854260000000000000000000000000 gm85_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 942420854827884418093723874512252000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (85 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((942420854827884418093723874512252000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 942420854827884418093723874512252000000000000000000000000 gm85_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (85 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg85 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
            if yzBoundary 0 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((85 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((85 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((20277054569819866366535185811042676620467646778328713376871145596000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp85 (fun b ↦
    if yzBoundary 0 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ85]
  rw [kzero _ gm85_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb85_0_4_0 (add_le_add cb85_1_3_0 (add_le_add cb85_2_2_0 (add_le_add cb85_3_1_0 (add_le_add gb85_0 (add_le_add gb85_1 (add_le_add gb85_2 gb85_3))))))) (le_of_eq (by push_cast; ring)))

theorem hsp86 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) + g (⟨![2,1,1], by decide +kernel⟩) + g (⟨![2,2,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩), (⟨![2,1,1], by decide +kernel⟩), (⟨![2,2,0], by decide +kernel⟩)} := by
    decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

theorem hJ86 : ∀ g : Fin (2 * 2 ^ (2 - 1) + 1) → ℝ,
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have hu : (Finset.univ : Finset (Fin (2 * 2 ^ (2 - 1) + 1))) = {0, 1, 2, 3, 4} := by decide +kernel
  intro g
  rw [hu, Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  ring

theorem cm86_0_4_0 :
    ∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 31109035174110108906082036628590000000000000000000000000 := by
  decide +kernel

theorem cb86_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((31109035174110108906082036628590000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31109035174110108906082036628590000000000000000000000000 cm86_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm86_1_3_0 :
    ∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1505653919475500561670862654494500000000000000000000000000 := by
  decide +kernel

theorem cb86_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1505653919475500561670862654494500000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1505653919475500561670862654494500000000000000000000000000 cm86_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm86_2_2_0 :
    ∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 807916280843728945321055308876910000000000000000000000000 := by
  decide +kernel

theorem cb86_2_2_0 :
    ((∑ w, mu3 2 1 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((807916280843728945321055308876910000000000000000000000000 * 378230719817571483520127227000 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![2,2,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 4 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((378230719817571483520127227000 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 807916280843728945321055308876910000000000000000000000000 cm86_2_2_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (86 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm86_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 31109035174110108906082036628590000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (86 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_1 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((31109035174110108906082036628590000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31109035174110108906082036628590000000000000000000000000 gm86_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1505653919475500561670862654494500000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (86 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1505653919475500561670862654494500000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1505653919475500561670862654494500000000000000000000000000 gm86_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 807916280843728945321055308876910000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (86 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((807916280843728945321055308876910000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 807916280843728945321055308876910000000000000000000000000 gm86_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (86 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg86 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
            if yzBoundary 0 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((86 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((86 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1930786557855515241463826892988208715008761042066732295466431630000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp86 (fun b ↦
    if yzBoundary 0 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ86]
  rw [kzero _ gm86_0]
  rw [kzero _ gm86_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb86_0_4_0 (add_le_add cb86_1_3_0 (add_le_add cb86_2_2_0 (add_le_add gb86_1 (add_le_add gb86_2 gb86_3))))) (le_of_eq (by push_cast; ring)))

theorem hsp87 : ∀ g : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)) → ℝ,
    ∑ c, g c = g (⟨![0,3,1], by decide +kernel⟩) + g (⟨![0,4,0], by decide +kernel⟩) + g (⟨![1,2,1], by decide +kernel⟩) + g (⟨![1,3,0], by decide +kernel⟩) := by
  have hu : (Finset.univ : Finset (Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)))) = {(⟨![0,3,1], by decide +kernel⟩), (⟨![0,4,0], by decide +kernel⟩), (⟨![1,2,1], by decide +kernel⟩), (⟨![1,3,0], by decide +kernel⟩)} := by
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

theorem cm87_0_4_0 :
    ∑ w, mu3 2 1 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25074871983320512306913901122566000000000000000000000000 := by
  decide +kernel

theorem cb87_0_4_0 :
    ((∑ w, mu3 2 1 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25074871983320512306913901122566000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25074871983320512306913901122566000000000000000000000000 cm87_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm87_1_3_0 :
    ∑ w, mu3 2 1 (⟨(87 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84596576188481519544086098877434000000000000000000000000 := by
  decide +kernel

theorem cb87_1_3_0 :
    ((∑ w, mu3 2 1 (⟨(87 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 (⟨(87 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84596576188481519544086098877434000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![1,3,0], by decide +kernel⟩) (rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84596576188481519544086098877434000000000000000000000000 cm87_1_3_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_0 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 0 then mu3 2 1 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (87 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_1 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 1 then mu3 2 1 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (87 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_2 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25074871983320512306913901122566000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 2 then mu3 2 1 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (87 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_2 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25074871983320512306913901122566000000000000000000000000 * 121937762094759851802294409 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((121937762094759851802294409 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25074871983320512306913901122566000000000000000000000000 gm87_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_3 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84596576188481519544086098877434000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 3 then mu3 2 1 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (87 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_3 :
    ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84596576188481519544086098877434000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84596576188481519544086098877434000000000000000000000000 gm87_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_4 :
    ∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 2).val = 0) ∧ (c.val 1).val = 4 then mu3 2 1 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp1 (87 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg87 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
            if yzBoundary 0 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr ((87 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr ((87 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((117278814113915598262944449672942478296875388722558950263920664000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp87 (fun b ↦
    if yzBoundary 0 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 1 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 1 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(87 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [if_neg (show ¬ yzBoundary 0 (⟨(87 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 0 (⟨(87 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from rfl)]
  rw [hJ87]
  rw [kzero _ gm87_0]
  rw [kzero _ gm87_1]
  rw [kzero _ gm87_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb87_0_4_0 (add_le_add cb87_1_3_0 (add_le_add gb87_2 gb87_3))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 2 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((202842711502579742189383710777325327156450511744964153679126676578000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg66 (add_le_add L3K.reg67 (add_le_add L3K.reg68 (add_le_add L3K.reg69 (add_le_add L3K.reg70 (add_le_add L3K.reg71 (add_le_add L3K.reg72 (add_le_add L3K.reg73 (add_le_add L3K.reg74 (add_le_add L3K.reg75 (add_le_add L3K.reg76 (add_le_add L3K.reg77 (add_le_add L3K.reg78 (add_le_add L3K.reg79 (add_le_add L3K.reg80 (add_le_add L3K.reg81 (add_le_add L3K.reg82 (add_le_add L3K.reg83 (add_le_add L3K.reg84 (add_le_add L3K.reg85 (add_le_add L3K.reg86 L3K.reg87))))))))))))))))))))) (le_of_eq (by push_cast; ring))
