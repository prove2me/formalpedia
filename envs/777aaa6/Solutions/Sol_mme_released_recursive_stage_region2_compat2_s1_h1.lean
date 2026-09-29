-- Prove2me | solution 1 for mme_released_recursive_stage_region2_compat2_s1_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T15:08:12.08924+00:00
-- url     : https://prove2.me/submissions/dc09b14a-0979-4666-a1b4-b5d0ae336f8b

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

theorem hgrp2 (rr : Fin 88) (jj : Fin (2 * 2 ^ (2 - 1) + 1))
    (w : CompleteSplit.CompleteWord 2) :
    partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)
        (Sum.inr (rr, jj)) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 rr),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = jj.val then mu3 2 2 ⟨rr, c⟩ w else 0 := by
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



noncomputable abbrev MU := partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)

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
    (hb : yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)))
    (e : CompleteSplit.CompleteWord 2 → Fin 4 → ℤ) (q : ℚ)
    (h : regCeilG (freqQ MU (Sum.inl ⟨⟨a, b⟩, hb⟩)) e ≤ q) (mass : ℕ)
    (hm : ∑ w, mu3 2 2 ⟨a, b⟩ w = mass) :
    ((∑ w, mu3 2 2 ⟨a, b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨a, b⟩) w : ℚ) : ℝ)) ≤
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

theorem cm66_0_1_3 :
    ∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 74405241811723551768439969281056000000000000000000000000 := by
  decide +kernel

theorem cb66_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((74405241811723551768439969281056000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 74405241811723551768439969281056000000000000000000000000 cm66_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_0_2_2 :
    ∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 500465365893396959919300788821680000000000000000000000000 := by
  decide +kernel

theorem cb66_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((500465365893396959919300788821680000000000000000000000000 * 417450655247866673393726470683 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then 4 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (13 : Int) else if k.val = 1 then -8 else if k.val = 2 then 1 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 5 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((417450655247866673393726470683 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 500465365893396959919300788821680000000000000000000000000 cm66_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_1_0_3 :
    ∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 549995053065520903236028835974660000000000000000000000000 := by
  decide +kernel

theorem cb66_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((549995053065520903236028835974660000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 549995053065520903236028835974660000000000000000000000000 cm66_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_2_0_2 :
    ∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 7321777961523489319463923482846068000000000000000000000000 := by
  decide +kernel

theorem cb66_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((7321777961523489319463923482846068000000000000000000000000 * 433853012142150345798457041644 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-20 : Int) else if k.val = 1 then 8 else if k.val = 2 then 5 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((433853012142150345798457041644 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7321777961523489319463923482846068000000000000000000000000 cm66_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm66_3_0_1 :
    ∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 500465365893396959919300788821680000000000000000000000000 := by
  decide +kernel

theorem cb66_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(66 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(66 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((500465365893396959919300788821680000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (66 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 500465365893396959919300788821680000000000000000000000000 cm66_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 624400294877244455004468805255716000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((624400294877244455004468805255716000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 624400294877244455004468805255716000000000000000000000000 gm66_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21545192411915330147928230405922604000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21545192411915330147928230405922604000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21545192411915330147928230405922604000000000000000000000000 gm66_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 14223414450391840828464306923076536000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb66_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((14223414450391840828464306923076536000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((66 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14223414450391840828464306923076536000000000000000000000000 gm66_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm66_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm66_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(66 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (66 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg66 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (66 : Fin 88)),
            if yzBoundary 1 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((66 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((66 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((19099181853976550021943274336406929954991662582499803831450788996000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp66 (fun b ↦
    if yzBoundary 1 (⟨(66 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(66 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(66 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(66 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(66 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ66]
  rw [kzero _ gm66_3]
  rw [kzero _ gm66_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb66_0_1_3 (add_le_add cb66_0_2_2 (add_le_add cb66_1_0_3 (add_le_add cb66_2_0_2 (add_le_add cb66_3_0_1 (add_le_add gb66_0 (add_le_add gb66_1 gb66_2))))))) (le_of_eq (by push_cast; ring)))

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

theorem cm67_0_0_4 :
    ∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6993995270709043528801972218468000000000000000000000000 := by
  decide +kernel

theorem cb67_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(67 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6993995270709043528801972218468000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6993995270709043528801972218468000000000000000000000000 cm67_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm67_0_1_3 :
    ∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1436808212050721007093743670245932000000000000000000000000 := by
  decide +kernel

theorem cb67_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(67 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1436808212050721007093743670245932000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat33.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 1436808212050721007093743670245932000000000000000000000000 cm67_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm67_0_2_2 :
    ∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 8883185266873734636288306871301048000000000000000000000000 := by
  decide +kernel

theorem cb67_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(67 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((8883185266873734636288306871301048000000000000000000000000 * 384190088254371090359919228695 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((384190088254371090359919228695 : ℚ)/10^30) mme_released_recursive_level3_compat34.1 8883185266873734636288306871301048000000000000000000000000 cm67_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm67_0_3_1 :
    ∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 270629170984105308125147486234552000000000000000000000000 := by
  decide +kernel

theorem cb67_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((270629170984105308125147486234552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.1 270629170984105308125147486234552000000000000000000000000 cm67_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm67_1_0_3 :
    ∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 270629170984105308125147486234552000000000000000000000000 := by
  decide +kernel

theorem cb67_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(67 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(67 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((270629170984105308125147486234552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (67 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.1 270629170984105308125147486234552000000000000000000000000 cm67_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6993995270709043528801972218468000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6993995270709043528801972218468000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.1 6993995270709043528801972218468000000000000000000000000 gm67_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1436808212050721007093743670245932000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1436808212050721007093743670245932000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.1 1436808212050721007093743670245932000000000000000000000000 gm67_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8883185266873734636288306871301048000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb67_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8883185266873734636288306871301048000000000000000000000000 * 15742589229363845045481075427 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((67 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15742589229363845045481075427 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.1 8883185266873734636288306871301048000000000000000000000000 gm67_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm67_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm67_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(67 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (67 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg67 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (67 : Fin 88)),
            if yzBoundary 1 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((67 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((67 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((5919686884431361677219277373739822901181125484484572656050144216000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp67 (fun b ↦
    if yzBoundary 1 (⟨(67 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(67 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(67 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(67 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ67]
  rw [kzero _ gm67_3]
  rw [kzero _ gm67_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb67_0_0_4 (add_le_add cb67_0_1_3 (add_le_add cb67_0_2_2 (add_le_add cb67_0_3_1 (add_le_add cb67_1_0_3 (add_le_add gb67_0 (add_le_add gb67_1 gb67_2))))))) (le_of_eq (by push_cast; ring)))

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

theorem cm68_0_2_2 :
    ∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 668242182960679888598645363219280000000000000000000000000 := by
  decide +kernel

theorem cb68_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((668242182960679888598645363219280000000000000000000000000 * 252399067287714795311855692059 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 4 else if k.val = 2 then 0 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 4 else if k.val = 2 then -1 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((252399067287714795311855692059 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.1 668242182960679888598645363219280000000000000000000000000 cm68_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_0_3_1 :
    ∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 93704815540746430923055573617552000000000000000000000000 := by
  decide +kernel

theorem cb68_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((93704815540746430923055573617552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 93704815540746430923055573617552000000000000000000000000 cm68_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_2_0_2 :
    ∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 718843348779305789483012687580504000000000000000000000000 := by
  decide +kernel

theorem cb68_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((718843348779305789483012687580504000000000000000000000000 * 424748145654778332691563475697 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -2 else 4) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((424748145654778332691563475697 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 718843348779305789483012687580504000000000000000000000000 cm68_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm68_3_0_1 :
    ∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 93704815540746430923055573617552000000000000000000000000 := by
  decide +kernel

theorem cb68_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((93704815540746430923055573617552000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (68 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 93704815540746430923055573617552000000000000000000000000 cm68_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11570837310763205875514216246492064000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11570837310763205875514216246492064000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11570837310763205875514216246492064000000000000000000000000 gm68_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 38976330446566749198949456359780768000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((38976330446566749198949456359780768000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38976330446566749198949456359780768000000000000000000000000 gm68_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 10183751779023220197432558195692280000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb68_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((10183751779023220197432558195692280000000000000000000000000 * 181365399969603393558148116066 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((68 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-22 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181365399969603393558148116066 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 10183751779023220197432558195692280000000000000000000000000 gm68_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm68_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm68_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(68 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (68 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg68 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (68 : Fin 88)),
            if yzBoundary 1 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((68 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((68 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((29467207312709982279887672620634640593126782251500678999910418968000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp68 (fun b ↦
    if yzBoundary 1 (⟨(68 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(68 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(68 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(68 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(68 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ68]
  rw [kzero _ gm68_3]
  rw [kzero _ gm68_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb68_0_2_2 (add_le_add cb68_0_3_1 (add_le_add cb68_2_0_2 (add_le_add cb68_3_0_1 (add_le_add gb68_0 (add_le_add gb68_1 gb68_2)))))) (le_of_eq (by push_cast; ring)))

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

theorem cm69_0_2_2 :
    ∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 2037727006025249471743123008646860000000000000000000000000 := by
  decide +kernel

theorem cb69_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((2037727006025249471743123008646860000000000000000000000000 * 315882209807202497279138071810 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((315882209807202497279138071810 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2037727006025249471743123008646860000000000000000000000000 cm69_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_0_3_1 :
    ∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 506855188054333336855644032483640000000000000000000000000 := by
  decide +kernel

theorem cb69_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(69 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((506855188054333336855644032483640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 506855188054333336855644032483640000000000000000000000000 cm69_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_0_4_0 :
    ∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4641148990723088437724181837240000000000000000000000000 := by
  decide +kernel

theorem cb69_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4641148990723088437724181837240000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4641148990723088437724181837240000000000000000000000000 cm69_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm69_2_0_2 :
    ∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4641148990723088437724181837240000000000000000000000000 := by
  decide +kernel

theorem cb69_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4641148990723088437724181837240000000000000000000000000 * 347357124830462612737914012625 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (69 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then -6 else if k.val = 2 then 8 else 1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 3 else if k.val = 2 then 7 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((347357124830462612737914012625 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4641148990723088437724181837240000000000000000000000000 cm69_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2606345658701701798224711842308380000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2606345658701701798224711842308380000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2606345658701701798224711842308380000000000000000000000000 gm69_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8387324682769369916339483919225120000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8387324682769369916339483919225120000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8387324682769369916339483919225120000000000000000000000000 gm69_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 568618652676452326481588833661520000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb69_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((568618652676452326481588833661520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((69 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 568618652676452326481588833661520000000000000000000000000 gm69_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm69_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm69_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(69 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (69 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg69 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (69 : Fin 88)),
            if yzBoundary 1 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((69 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((69 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((6810269546670866303234023618301762381958211379077463373461074140000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp69 (fun b ↦
    if yzBoundary 1 (⟨(69 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(69 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(69 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(69 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ69]
  rw [kzero _ gm69_3]
  rw [kzero _ gm69_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb69_0_2_2 (add_le_add cb69_0_3_1 (add_le_add cb69_0_4_0 (add_le_add cb69_2_0_2 (add_le_add gb69_0 (add_le_add gb69_1 gb69_2)))))) (le_of_eq (by push_cast; ring)))

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

theorem cm70_0_3_1 :
    ∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 804875533400573679692450356030962000000000000000000000000 := by
  decide +kernel

theorem cb70_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((804875533400573679692450356030962000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 804875533400573679692450356030962000000000000000000000000 cm70_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_0_4_0 :
    ∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 21309305200459256409010112555525000000000000000000000000 := by
  decide +kernel

theorem cb70_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((21309305200459256409010112555525000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21309305200459256409010112555525000000000000000000000000 cm70_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm70_3_0_1 :
    ∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 21309305200459256409010112555525000000000000000000000000 := by
  decide +kernel

theorem cb70_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((21309305200459256409010112555525000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (70 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21309305200459256409010112555525000000000000000000000000 cm70_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32863701327736274361589989887444475000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32863701327736274361589989887444475000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32863701327736274361589989887444475000000000000000000000000 gm70_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 32058825794335700681897539531413513000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb70_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((32058825794335700681897539531413513000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((70 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 32058825794335700681897539531413513000000000000000000000000 gm70_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm70_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm70_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm70_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(70 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (70 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg70 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (70 : Fin 88)),
            if yzBoundary 1 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((70 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((70 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((22794152402903919479775960617840735332557754304033987000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp70 (fun b ↦
    if yzBoundary 1 (⟨(70 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(70 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(70 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(70 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(70 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ70]
  rw [kzero _ gm70_2]
  rw [kzero _ gm70_3]
  rw [kzero _ gm70_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb70_0_3_1 (add_le_add cb70_0_4_0 (add_le_add cb70_3_0_1 (add_le_add gb70_0 gb70_1)))) (le_of_eq (by push_cast; ring)))

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

theorem cm71_0_2_2 :
    ∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 189379990614143106552908278024320000000000000000000000000 := by
  decide +kernel

theorem cb71_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((189379990614143106552908278024320000000000000000000000000 * 304700861040634478173220448870 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 3 else if k.val = 2 then -8 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304700861040634478173220448870 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 189379990614143106552908278024320000000000000000000000000 cm71_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm71_0_3_1 :
    ∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 341366924695263117828679387205880000000000000000000000000 := by
  decide +kernel

theorem cb71_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((341366924695263117828679387205880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 341366924695263117828679387205880000000000000000000000000 cm71_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm71_0_4_0 :
    ∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 7707852404896207898412334769800000000000000000000000000 := by
  decide +kernel

theorem cb71_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((7707852404896207898412334769800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (71 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7707852404896207898412334769800000000000000000000000000 cm71_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 189379990614143106552908278024320000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((189379990614143106552908278024320000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 189379990614143106552908278024320000000000000000000000000 gm71_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 341366924695263117828679387205880000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((341366924695263117828679387205880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 341366924695263117828679387205880000000000000000000000000 gm71_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 7707852404896207898412334769800000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb71_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((7707852404896207898412334769800000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((71 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7707852404896207898412334769800000000000000000000000000 gm71_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm71_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm71_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(71 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (71 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg71 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (71 : Fin 88)),
            if yzBoundary 1 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((71 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((71 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((530939288981878275947451433519113331831419850856645610535936400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp71 (fun b ↦
    if yzBoundary 1 (⟨(71 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(71 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(71 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(71 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(71 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ71]
  rw [kzero _ gm71_3]
  rw [kzero _ gm71_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb71_0_2_2 (add_le_add cb71_0_3_1 (add_le_add cb71_0_4_0 (add_le_add gb71_0 (add_le_add gb71_1 gb71_2))))) (le_of_eq (by push_cast; ring)))

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

theorem cm72_0_3_1 :
    ∑ w, mu3 2 2 (⟨(72 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 724461817410532619326887026231928000000000000000000000000 := by
  decide +kernel

theorem cb72_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(72 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(72 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((724461817410532619326887026231928000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 724461817410532619326887026231928000000000000000000000000 cm72_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm72_0_4_0 :
    ∑ w, mu3 2 2 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 29115794560556955198381523109096000000000000000000000000 := by
  decide +kernel

theorem cb72_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((29115794560556955198381523109096000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (72 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 29115794560556955198381523109096000000000000000000000000 cm72_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2038934452346628617325618476890904000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2038934452346628617325618476890904000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2038934452346628617325618476890904000000000000000000000000 gm72_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1343588429496652953197112973768072000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb72_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1343588429496652953197112973768072000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((72 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1343588429496652953197112973768072000000000000000000000000 gm72_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm72_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm72_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm72_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(72 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (72 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg72 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (72 : Fin 88)),
            if yzBoundary 1 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((72 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((72 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1433463197900014436726525210742003501106699504442812000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp72 (fun b ↦
    if yzBoundary 1 (⟨(72 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(72 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(72 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(72 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(72 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ72]
  rw [kzero _ gm72_2]
  rw [kzero _ gm72_3]
  rw [kzero _ gm72_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb72_0_3_1 (add_le_add cb72_0_4_0 (add_le_add gb72_0 gb72_1))) (le_of_eq (by push_cast; ring)))

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

theorem cm73_0_3_1 :
    ∑ w, mu3 2 2 (⟨(73 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84537062021935542576814436831808000000000000000000000000 := by
  decide +kernel

theorem cb73_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(73 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(73 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84537062021935542576814436831808000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84537062021935542576814436831808000000000000000000000000 cm73_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm73_0_4_0 :
    ∑ w, mu3 2 2 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25767992860467236471185563168192000000000000000000000000 := by
  decide +kernel

theorem cb73_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25767992860467236471185563168192000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (73 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25767992860467236471185563168192000000000000000000000000 cm73_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84537062021935542576814436831808000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84537062021935542576814436831808000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84537062021935542576814436831808000000000000000000000000 gm73_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25767992860467236471185563168192000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb73_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25767992860467236471185563168192000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((73 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25767992860467236471185563168192000000000000000000000000 gm73_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm73_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm73_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm73_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(73 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (73 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg73 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (73 : Fin 88)),
            if yzBoundary 1 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((73 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((73 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76457637793247516007696176381674610256005420127624000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp73 (fun b ↦
    if yzBoundary 1 (⟨(73 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(73 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(73 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(73 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(73 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(73 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(73 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ73]
  rw [kzero _ gm73_2]
  rw [kzero _ gm73_3]
  rw [kzero _ gm73_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb73_0_3_1 (add_le_add cb73_0_4_0 (add_le_add gb73_0 gb73_1))) (le_of_eq (by push_cast; ring)))

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

theorem cm74_0_0_4 :
    ∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 26498908842952077486635675903136000000000000000000000000 := by
  decide +kernel

theorem cb74_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(74 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((26498908842952077486635675903136000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (74 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 26498908842952077486635675903136000000000000000000000000 cm74_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm74_0_1_3 :
    ∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84946679479888224479364324096864000000000000000000000000 := by
  decide +kernel

theorem cb74_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(74 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84946679479888224479364324096864000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (74 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat34.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 84946679479888224479364324096864000000000000000000000000 cm74_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm74_1_0_3 :
    ∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84946679479888224479364324096864000000000000000000000000 := by
  decide +kernel

theorem cb74_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(74 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(74 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84946679479888224479364324096864000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (74 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.1 84946679479888224479364324096864000000000000000000000000 cm74_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 26498908842952077486635675903136000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb74_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((26498908842952077486635675903136000000000000000000000000 * 203944572754291408022548221466 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((74 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-19 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else -1) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((203944572754291408022548221466 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.1 26498908842952077486635675903136000000000000000000000000 gm74_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm74_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm74_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(74 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (74 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg74 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (74 : Fin 88)),
            if yzBoundary 1 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((74 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((74 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((123165411401258544398555982314995497085279449060933046336401696000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp74 (fun b ↦
    if yzBoundary 1 (⟨(74 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(74 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(74 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(74 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(74 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(74 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(74 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ74]
  rw [kzero _ gm74_0]
  rw [kzero _ gm74_1]
  rw [kzero _ gm74_3]
  rw [kzero _ gm74_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb74_0_0_4 (add_le_add cb74_0_1_3 (add_le_add cb74_1_0_3 gb74_2))) (le_of_eq (by push_cast; ring)))

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

theorem cm75_0_0_4 :
    ∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 41498039006805836133818161487008000000000000000000000000 := by
  decide +kernel

theorem cb75_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((41498039006805836133818161487008000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.1 41498039006805836133818161487008000000000000000000000000 cm75_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm75_0_1_3 :
    ∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 998228709063249560675263848831468000000000000000000000000 := by
  decide +kernel

theorem cb75_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((998228709063249560675263848831468000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.1 998228709063249560675263848831468000000000000000000000000 cm75_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm75_1_0_3 :
    ∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1782119151770451948442917989681524000000000000000000000000 := by
  decide +kernel

theorem cb75_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1782119151770451948442917989681524000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.1 1782119151770451948442917989681524000000000000000000000000 cm75_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm75_2_0_2 :
    ∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 998228709063249560675263848831468000000000000000000000000 := by
  decide +kernel

theorem cb75_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(75 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(75 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((998228709063249560675263848831468000000000000000000000000 * 432787963874934289717949721388 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (75 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then 7 else if k.val = 2 then 8 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then -3 else if k.val = 2 then 3 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432787963874934289717949721388 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.1 998228709063249560675263848831468000000000000000000000000 cm75_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 41498039006805836133818161487008000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb75_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((41498039006805836133818161487008000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((75 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.1 41498039006805836133818161487008000000000000000000000000 gm75_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1782119151770451948442917989681524000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb75_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1782119151770451948442917989681524000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((75 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.1 1782119151770451948442917989681524000000000000000000000000 gm75_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm75_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm75_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(75 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (75 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg75 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (75 : Fin 88)),
            if yzBoundary 1 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((75 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((75 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2387975899926077433710265835447499853825178581381742153025217308000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp75 (fun b ↦
    if yzBoundary 1 (⟨(75 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(75 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(75 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(75 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(75 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(75 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ75]
  rw [kzero _ gm75_0]
  rw [kzero _ gm75_3]
  rw [kzero _ gm75_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb75_0_0_4 (add_le_add cb75_0_1_3 (add_le_add cb75_1_0_3 (add_le_add cb75_2_0_2 (add_le_add gb75_1 gb75_2))))) (le_of_eq (by push_cast; ring)))

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

theorem cm76_0_0_4 :
    ∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 3895259040618605539168576104216000000000000000000000000 := by
  decide +kernel

theorem cb76_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((3895259040618605539168576104216000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3895259040618605539168576104216000000000000000000000000 cm76_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_0_1_3 :
    ∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 150735404086119508495268029619880000000000000000000000000 := by
  decide +kernel

theorem cb76_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((150735404086119508495268029619880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 150735404086119508495268029619880000000000000000000000000 cm76_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_1_0_3 :
    ∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 803285903733389833385614169700450000000000000000000000000 := by
  decide +kernel

theorem cb76_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((803285903733389833385614169700450000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 803285903733389833385614169700450000000000000000000000000 cm76_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_2_0_2 :
    ∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 4968651736663325298705949224575454000000000000000000000000 := by
  decide +kernel

theorem cb76_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(76 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((4968651736663325298705949224575454000000000000000000000000 * 384191498826825485853275239088 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 1 else if k.val = 2 then -8 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((384191498826825485853275239088 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4968651736663325298705949224575454000000000000000000000000 cm76_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm76_3_0_1 :
    ∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 150735404086119508495268029619880000000000000000000000000 := by
  decide +kernel

theorem cb76_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(76 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(76 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((150735404086119508495268029619880000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (76 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 150735404086119508495268029619880000000000000000000000000 cm76_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 3895259040618605539168576104216000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((3895259040618605539168576104216000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 3895259040618605539168576104216000000000000000000000000 gm76_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 803285903733389833385614169700450000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((803285903733389833385614169700450000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 803285903733389833385614169700450000000000000000000000000 gm76_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 4968651736663325298705949224575454000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb76_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((4968651736663325298705949224575454000000000000000000000000 * 15741992933365147703115809910 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((76 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 6 else if k.val = 2 then -7 else -4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15741992933365147703115809910 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 4968651736663325298705949224575454000000000000000000000000 gm76_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm76_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm76_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(76 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (76 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg76 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (76 : Fin 88)),
            if yzBoundary 1 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((76 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((76 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((3309684597802508101407279653169577185050920875109340972499398076000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp76 (fun b ↦
    if yzBoundary 1 (⟨(76 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(76 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(76 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(76 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(76 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(76 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(76 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ76]
  rw [kzero _ gm76_3]
  rw [kzero _ gm76_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb76_0_0_4 (add_le_add cb76_0_1_3 (add_le_add cb76_1_0_3 (add_le_add cb76_2_0_2 (add_le_add cb76_3_0_1 (add_le_add gb76_0 (add_le_add gb76_1 gb76_2))))))) (le_of_eq (by push_cast; ring)))

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

theorem cm77_2_0_2 :
    ∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 149577046232736840793649670877938000000000000000000000000 := by
  decide +kernel

theorem cb77_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(77 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((149577046232736840793649670877938000000000000000000000000 * 304734024197627296084511839774 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -3 else if k.val = 2 then -3 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-39 : Int) else if k.val = 1 then 3 else if k.val = 2 then 3 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((304734024197627296084511839774 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 149577046232736840793649670877938000000000000000000000000 cm77_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_3_0_1 :
    ∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 269734995016178260649830923859038000000000000000000000000 := by
  decide +kernel

theorem cb77_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(77 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((269734995016178260649830923859038000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 269734995016178260649830923859038000000000000000000000000 cm77_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm77_4_0_0 :
    ∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6087774109725946354519405263024000000000000000000000000 := by
  decide +kernel

theorem cb77_4_0_0 :
    ((∑ w, mu3 2 2 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6087774109725946354519405263024000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (77 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6087774109725946354519405263024000000000000000000000000 cm77_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 149577046232736840793649670877938000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((149577046232736840793649670877938000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 149577046232736840793649670877938000000000000000000000000 gm77_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 269734995016178260649830923859038000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((269734995016178260649830923859038000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 269734995016178260649830923859038000000000000000000000000 gm77_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6087774109725946354519405263024000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb77_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6087774109725946354519405263024000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((77 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6087774109725946354519405263024000000000000000000000000 gm77_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm77_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm77_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(77 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (77 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg77 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (77 : Fin 88)),
            if yzBoundary 1 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((77 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((77 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((419513317813726167214830037115847730086538983654328924331642370000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp77 (fun b ↦
    if yzBoundary 1 (⟨(77 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(77 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(77 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(77 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(77 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [hJ77]
  rw [kzero _ gm77_3]
  rw [kzero _ gm77_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb77_2_0_2 (add_le_add cb77_3_0_1 (add_le_add cb77_4_0_0 (add_le_add gb77_0 (add_le_add gb77_1 gb77_2))))) (le_of_eq (by push_cast; ring)))

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

theorem cm78_3_0_1 :
    ∑ w, mu3 2 2 (⟨(78 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84448430638772369604075266185084000000000000000000000000 := by
  decide +kernel

theorem cb78_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(78 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(78 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84448430638772369604075266185084000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84448430638772369604075266185084000000000000000000000000 cm78_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm78_4_0_0 :
    ∑ w, mu3 2 2 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25796342675231138911924733814916000000000000000000000000 := by
  decide +kernel

theorem cb78_4_0_0 :
    ((∑ w, mu3 2 2 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25796342675231138911924733814916000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (78 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25796342675231138911924733814916000000000000000000000000 cm78_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84448430638772369604075266185084000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84448430638772369604075266185084000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84448430638772369604075266185084000000000000000000000000 gm78_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25796342675231138911924733814916000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb78_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25796342675231138911924733814916000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((78 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25796342675231138911924733814916000000000000000000000000 gm78_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm78_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm78_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm78_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(78 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (78 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg78 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (78 : Fin 88)),
            if yzBoundary 1 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((78 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((78 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76415853794071830142913790988630559365738273610708000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp78 (fun b ↦
    if yzBoundary 1 (⟨(78 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(78 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(78 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(78 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(78 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(78 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(78 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [hJ78]
  rw [kzero _ gm78_2]
  rw [kzero _ gm78_3]
  rw [kzero _ gm78_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb78_3_0_1 (add_le_add cb78_4_0_0 (add_le_add gb78_0 gb78_1))) (le_of_eq (by push_cast; ring)))

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

theorem cm79_0_0_4 :
    ∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 47537252991435830614508725002850000000000000000000000000 := by
  decide +kernel

theorem cb79_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(79 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((47537252991435830614508725002850000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 47537252991435830614508725002850000000000000000000000000 cm79_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm79_0_1_3 :
    ∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 2034996645763426817252607631184600000000000000000000000000 := by
  decide +kernel

theorem cb79_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(79 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((2034996645763426817252607631184600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2034996645763426817252607631184600000000000000000000000000 cm79_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm79_0_2_2 :
    ∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1144262517639148143782883643812550000000000000000000000000 := by
  decide +kernel

theorem cb79_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(79 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1144262517639148143782883643812550000000000000000000000000 * 432392354162788003815120758675 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else 6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -4 else if k.val = 2 then -2 else 6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((432392354162788003815120758675 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1144262517639148143782883643812550000000000000000000000000 cm79_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm79_1_0_3 :
    ∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1144262517639148143782883643812550000000000000000000000000 := by
  decide +kernel

theorem cb79_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(79 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(79 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1144262517639148143782883643812550000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (79 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1144262517639148143782883643812550000000000000000000000000 cm79_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm79_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 47537252991435830614508725002850000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((47537252991435830614508725002850000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 47537252991435830614508725002850000000000000000000000000 gm79_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2034996645763426817252607631184600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb79_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2034996645763426817252607631184600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((79 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2034996645763426817252607631184600000000000000000000000000 gm79_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm79_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm79_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(79 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (79 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg79 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (79 : Fin 88)),
            if yzBoundary 1 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((79 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((79 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((2731415202046673866457880890820221218313482974346354039979683400000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp79 (fun b ↦
    if yzBoundary 1 (⟨(79 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(79 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(79 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(79 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(79 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(79 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ79]
  rw [kzero _ gm79_0]
  rw [kzero _ gm79_3]
  rw [kzero _ gm79_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb79_0_0_4 (add_le_add cb79_0_1_3 (add_le_add cb79_0_2_2 (add_le_add cb79_1_0_3 (add_le_add gb79_1 gb79_2))))) (le_of_eq (by push_cast; ring)))

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

theorem cm80_0_1_3 :
    ∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 85878687665783984425604424681600000000000000000000000000 := by
  decide +kernel

theorem cb80_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((85878687665783984425604424681600000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 85878687665783984425604424681600000000000000000000000000 cm80_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_0_2_2 :
    ∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 577831580946665393111214833510400000000000000000000000000 := by
  decide +kernel

theorem cb80_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(80 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((577831580946665393111214833510400000000000000000000000000 * 416948444831941245835691424327 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 4) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((416948444831941245835691424327 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 577831580946665393111214833510400000000000000000000000000 cm80_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_1_0_3 :
    ∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 631414952879840861408084858912000000000000000000000000000 := by
  decide +kernel

theorem cb80_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((631414952879840861408084858912000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 631414952879840861408084858912000000000000000000000000000 cm80_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_2_0_2 :
    ∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 8407926260053923617272606915132800000000000000000000000000 := by
  decide +kernel

theorem cb80_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((8407926260053923617272606915132800000000000000000000000000 * 434242642625873037010034045726 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-3 : Int) else if k.val = 1 then -2 else if k.val = 2 then 5 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -8 else if k.val = 2 then -2 else -1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((434242642625873037010034045726 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 8407926260053923617272606915132800000000000000000000000000 cm80_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm80_3_0_1 :
    ∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 577831580946665393111214833510400000000000000000000000000 := by
  decide +kernel

theorem cb80_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((577831580946665393111214833510400000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (80 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 577831580946665393111214833510400000000000000000000000000 cm80_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 717293640545624845833689283593600000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((717293640545624845833689283593600000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 717293640545624845833689283593600000000000000000000000000 gm80_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 24736829875987252420255095882896000000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((24736829875987252420255095882896000000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 24736829875987252420255095882896000000000000000000000000000 gm80_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 16328903615933328802982488967763200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb80_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((16328903615933328802982488967763200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((80 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 16328903615933328802982488967763200000000000000000000000000 gm80_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm80_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm80_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(80 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (80 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg80 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (80 : Fin 88)),
            if yzBoundary 1 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((80 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((80 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((21935982377500824559057244875091688890307515381585775909689411200000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp80 (fun b ↦
    if yzBoundary 1 (⟨(80 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(80 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(80 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(80 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(80 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ80]
  rw [kzero _ gm80_3]
  rw [kzero _ gm80_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb80_0_1_3 (add_le_add cb80_0_2_2 (add_le_add cb80_1_0_3 (add_le_add cb80_2_0_2 (add_le_add cb80_3_0_1 (add_le_add gb80_0 (add_le_add gb80_1 gb80_2))))))) (le_of_eq (by push_cast; ring)))

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

theorem cm81_0_2_2 :
    ∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 12142251382117114678981186724904000000000000000000000000 := by
  decide +kernel

theorem cb81_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((12142251382117114678981186724904000000000000000000000000 * 137387386985434489926214337 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -2) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -8 else if k.val = 2 then -7 else -2) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((137387386985434489926214337 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12142251382117114678981186724904000000000000000000000000 cm81_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_2_0_2 :
    ∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 5336919835023709980018128280938412000000000000000000000000 := by
  decide +kernel

theorem cb81_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((5336919835023709980018128280938412000000000000000000000000 * 335902537728583276591995078043 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 8) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -7 else if k.val = 2 then 1 else 7) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then 1 else if k.val = 2 then 1 else 8) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((335902537728583276591995078043 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 5336919835023709980018128280938412000000000000000000000000 cm81_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_3_0_1 :
    ∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1370227681636159527352649902378565000000000000000000000000 := by
  decide +kernel

theorem cb81_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1370227681636159527352649902378565000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1370227681636159527352649902378565000000000000000000000000 cm81_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm81_4_0_0 :
    ∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 12142251382117114678981186724904000000000000000000000000 := by
  decide +kernel

theorem cb81_4_0_0 :
    ((∑ w, mu3 2 2 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((12142251382117114678981186724904000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (81 : Fin 88) (⟨![4,0,0], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 12142251382117114678981186724904000000000000000000000000 cm81_4_0_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6806680845816683343111599764263200000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6806680845816683343111599764263200000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 6806680845816683343111599764263200000000000000000000000000 gm81_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 21972399673517417846808188195645227000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((21972399673517417846808188195645227000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 21972399673517417846808188195645227000000000000000000000000 gm81_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1469761010792973363093471483324788000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb81_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1469761010792973363093471483324788000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((81 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1469761010792973363093471483324788000000000000000000000000 gm81_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm81_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm81_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(81 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (81 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg81 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (81 : Fin 88)),
            if yzBoundary 1 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((81 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((81 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((17972562922516821007905548783405124875508878294246786780540569360000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp81 (fun b ↦
    if yzBoundary 1 (⟨(81 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(81 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(81 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(81 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(81 : Fin 88), (⟨![4,0,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [hJ81]
  rw [kzero _ gm81_3]
  rw [kzero _ gm81_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb81_0_2_2 (add_le_add cb81_2_0_2 (add_le_add cb81_3_0_1 (add_le_add cb81_4_0_0 (add_le_add gb81_0 (add_le_add gb81_1 gb81_2)))))) (le_of_eq (by push_cast; ring)))

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

theorem cm82_0_0_4 :
    ∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 6982514479028264223519614939638000000000000000000000000 := by
  decide +kernel

theorem cb82_0_0_4 :
    ((∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((6982514479028264223519614939638000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,0,4], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 8 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat35.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 6982514479028264223519614939638000000000000000000000000 cm82_0_0_4) (le_of_eq ?_)
  push_cast
  ring

theorem cm82_0_1_3 :
    ∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 1441386111823449672488323295220784000000000000000000000000 := by
  decide +kernel

theorem cb82_0_1_3 :
    ((∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((1441386111823449672488323295220784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,1,3], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.1 1441386111823449672488323295220784000000000000000000000000 cm82_0_1_3) (le_of_eq ?_)
  push_cast
  ring

theorem cm82_0_2_2 :
    ∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 8906600255725053085581900755057762000000000000000000000000 := by
  decide +kernel

theorem cb82_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((8906600255725053085581900755057762000000000000000000000000 * 383795172109232593881470579277 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 5 else if k.val = 2 then 3 else -5) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -6 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((383795172109232593881470579277 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.1 8906600255725053085581900755057762000000000000000000000000 cm82_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm82_0_3_1 :
    ∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 270149827126840036524256334781816000000000000000000000000 := by
  decide +kernel

theorem cb82_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((270149827126840036524256334781816000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.1 270149827126840036524256334781816000000000000000000000000 cm82_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm82_1_0_3 :
    ∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 270149827126840036524256334781816000000000000000000000000 := by
  decide +kernel

theorem cb82_1_0_3 :
    ((∑ w, mu3 2 2 (⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((270149827126840036524256334781816000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (82 : Fin 88) (⟨![1,0,3], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 5 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 7 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.1 270149827126840036524256334781816000000000000000000000000 cm82_1_0_3) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 6982514479028264223519614939638000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((6982514479028264223519614939638000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.1 6982514479028264223519614939638000000000000000000000000 gm82_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1441386111823449672488323295220784000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1441386111823449672488323295220784000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.1 1441386111823449672488323295220784000000000000000000000000 gm82_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 8906600255725053085581900755057762000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb82_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((8906600255725053085581900755057762000000000000000000000000 * 15886555485788736328894661159 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((82 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (22 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else -6) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 0 else if k.val = 2 then -5 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((15886555485788736328894661159 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.1 8906600255725053085581900755057762000000000000000000000000 gm82_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm82_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm82_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(82 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (82 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg82 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (82 : Fin 88)),
            if yzBoundary 1 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((82 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((82 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((5932497998227271972024202271771934365719572210714905887967250364000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp82 (fun b ↦
    if yzBoundary 1 (⟨(82 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(82 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(82 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,0,4], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,1,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,0,3], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(82 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ82]
  rw [kzero _ gm82_3]
  rw [kzero _ gm82_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb82_0_0_4 (add_le_add cb82_0_1_3 (add_le_add cb82_0_2_2 (add_le_add cb82_0_3_1 (add_le_add cb82_1_0_3 (add_le_add gb82_0 (add_le_add gb82_1 gb82_2))))))) (le_of_eq (by push_cast; ring)))

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

theorem cm83_0_2_2 :
    ∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 763180712521234715272414333598400000000000000000000000000 := by
  decide +kernel

theorem cb83_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((763180712521234715272414333598400000000000000000000000000 * 250230608333483937205596061289 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 1) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 8 else if k.val = 2 then 1 else 1) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((250230608333483937205596061289 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 763180712521234715272414333598400000000000000000000000000 cm83_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_0_3_1 :
    ∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 106260345654008060462528337694080000000000000000000000000 := by
  decide +kernel

theorem cb83_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(83 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((106260345654008060462528337694080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106260345654008060462528337694080000000000000000000000000 cm83_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_2_0_2 :
    ∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 810491575813781471082071704028352000000000000000000000000 := by
  decide +kernel

theorem cb83_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((810491575813781471082071704028352000000000000000000000000 * 425437038168355752027150988962 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 4 else if k.val = 2 then -6 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (-33 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else 7) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((425437038168355752027150988962 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 810491575813781471082071704028352000000000000000000000000 cm83_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm83_3_0_1 :
    ∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 106260345654008060462528337694080000000000000000000000000 := by
  decide +kernel

theorem cb83_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((106260345654008060462528337694080000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (83 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 106260345654008060462528337694080000000000000000000000000 cm83_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 13141261070825323046106382895346624000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((13141261070825323046106382895346624000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 13141261070825323046106382895346624000000000000000000000000 gm83_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 44259712792212094730094177533918592000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((44259712792212094730094177533918592000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 44259712792212094730094177533918592000000000000000000000000 gm83_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 11567588782490306859751896857719872000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb83_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((11567588782490306859751896857719872000000000000000000000000 * 181584116514714293892649884756 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((83 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -6 else if k.val = 2 then -3 else 3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (9 : Int) else if k.val = 1 then -2 else if k.val = 2 then -5 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((181584116514714293892649884756 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 11567588782490306859751896857719872000000000000000000000000 gm83_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm83_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm83_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(83 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (83 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg83 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (83 : Fin 88)),
            if yzBoundary 1 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((83 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((83 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((33462077951016770621911816329856647682226918142908619466869726336000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp83 (fun b ↦
    if yzBoundary 1 (⟨(83 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(83 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(83 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(83 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(83 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ83]
  rw [kzero _ gm83_3]
  rw [kzero _ gm83_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb83_0_2_2 (add_le_add cb83_0_3_1 (add_le_add cb83_2_0_2 (add_le_add cb83_3_0_1 (add_le_add gb83_0 (add_le_add gb83_1 gb83_2)))))) (le_of_eq (by push_cast; ring)))

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

theorem cm84_0_2_2 :
    ∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 165382910392113540431910847930512000000000000000000000000 := by
  decide +kernel

theorem cb84_0_2_2 :
    ((∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((165382910392113540431910847930512000000000000000000000000 * 302931427151302858894710523887 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,2,2], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 0) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (-4 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -2) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((302931427151302858894710523887 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 165382910392113540431910847930512000000000000000000000000 cm84_0_2_2) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_0_3_1 :
    ∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 38534766625338705940848431671936000000000000000000000000 := by
  decide +kernel

theorem cb84_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((38534766625338705940848431671936000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38534766625338705940848431671936000000000000000000000000 cm84_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_0_4_0 :
    ∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 360962513921752762264364771520000000000000000000000000 := by
  decide +kernel

theorem cb84_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((360962513921752762264364771520000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360962513921752762264364771520000000000000000000000000 cm84_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm84_2_0_2 :
    ∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 360962513921752762264364771520000000000000000000000000 := by
  decide +kernel

theorem cb84_2_0_2 :
    ((∑ w, mu3 2 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((360962513921752762264364771520000000000000000000000000 * 343316850561363984211259942084 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (84 : Fin 88) (⟨![2,0,2], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -6) else if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (16 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else -3) else if 3 * (v 0).val + (v 1).val = 6 then (if k.val = 0 then (11 : Int) else if k.val = 1 then -8 else if k.val = 2 then 6 else -6) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((343316850561363984211259942084 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 360962513921752762264364771520000000000000000000000000 cm84_2_0_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 208065310400157116266751615843696000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((208065310400157116266751615843696000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 208065310400157116266751615843696000000000000000000000000 gm84_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 676217526345359162945119607097632000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((676217526345359162945119607097632000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 676217526345359162945119607097632000000000000000000000000 gm84_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 42682400008043575834840767913184000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb84_2 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((42682400008043575834840767913184000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((84 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 42682400008043575834840767913184000000000000000000000000 gm84_2) (le_of_eq ?_)
  push_cast
  ring

theorem gm84_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm84_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(84 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (84 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg84 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (84 : Fin 88)),
            if yzBoundary 1 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((84 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((84 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((545652142256364564457973564563724941008736496269509117201104032000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp84 (fun b ↦
    if yzBoundary 1 (⟨(84 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(84 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(84 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![0,2,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,1,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,0,2], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(84 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ84]
  rw [kzero _ gm84_3]
  rw [kzero _ gm84_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb84_0_2_2 (add_le_add cb84_0_3_1 (add_le_add cb84_0_4_0 (add_le_add cb84_2_0_2 (add_le_add gb84_0 (add_le_add gb84_1 gb84_2)))))) (le_of_eq (by push_cast; ring)))

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

theorem cm85_0_3_1 :
    ∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 942420854827884418093723874512252000000000000000000000000 := by
  decide +kernel

theorem cb85_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((942420854827884418093723874512252000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 942420854827884418093723874512252000000000000000000000000 cm85_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_0_4_0 :
    ∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25343893829624423990405482978108000000000000000000000000 := by
  decide +kernel

theorem cb85_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25343893829624423990405482978108000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25343893829624423990405482978108000000000000000000000000 cm85_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem cm85_3_0_1 :
    ∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25343893829624423990405482978108000000000000000000000000 := by
  decide +kernel

theorem cb85_3_0_1 :
    ((∑ w, mu3 2 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25343893829624423990405482978108000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (85 : Fin 88) (⟨![3,0,1], by decide +kernel⟩) (Or.inr rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25343893829624423990405482978108000000000000000000000000 cm85_3_0_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 38879425686533204184253594517021892000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((38879425686533204184253594517021892000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 38879425686533204184253594517021892000000000000000000000000 gm85_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 37937004831705319766159870642509640000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb85_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((37937004831705319766159870642509640000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((85 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 37937004831705319766159870642509640000000000000000000000000 gm85_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm85_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm85_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm85_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(85 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (85 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg85 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (85 : Fin 88)),
            if yzBoundary 1 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((85 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((85 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((26966731344962821267110071475906512600644185623907172000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp85 (fun b ↦
    if yzBoundary 1 (⟨(85 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(85 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(85 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_pos (show yzBoundary 1 (⟨(85 : Fin 88), (⟨![3,0,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inr rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(85 : Fin 88), (⟨![3,1,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ85]
  rw [kzero _ gm85_2]
  rw [kzero _ gm85_3]
  rw [kzero _ gm85_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb85_0_3_1 (add_le_add cb85_0_4_0 (add_le_add cb85_3_0_1 (add_le_add gb85_0 gb85_1)))) (le_of_eq (by push_cast; ring)))

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

theorem cm86_0_3_1 :
    ∑ w, mu3 2 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 807916280843728945321055308876910000000000000000000000000 := by
  decide +kernel

theorem cb86_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((807916280843728945321055308876910000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 807916280843728945321055308876910000000000000000000000000 cm86_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm86_0_4_0 :
    ∑ w, mu3 2 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 31109035174110108906082036628590000000000000000000000000 := by
  decide +kernel

theorem cb86_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((31109035174110108906082036628590000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (86 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 31109035174110108906082036628590000000000000000000000000 cm86_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 2313570200319229506991917963371410000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((2313570200319229506991917963371410000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 2313570200319229506991917963371410000000000000000000000000 gm86_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 1536762954649610670576944691123090000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb86_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((1536762954649610670576944691123090000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((86 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 1536762954649610670576944691123090000000000000000000000000 gm86_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm86_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm86_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm86_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(86 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (86 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg86 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (86 : Fin 88)),
            if yzBoundary 1 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((86 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((86 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((1625207801399656403544461237799020320503383649006674000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp86 (fun b ↦
    if yzBoundary 1 (⟨(86 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(86 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(86 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(86 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(86 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![2,1,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(86 : Fin 88), (⟨![2,2,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ86]
  rw [kzero _ gm86_2]
  rw [kzero _ gm86_3]
  rw [kzero _ gm86_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb86_0_3_1 (add_le_add cb86_0_4_0 (add_le_add gb86_0 gb86_1))) (le_of_eq (by push_cast; ring)))

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

theorem cm87_0_3_1 :
    ∑ w, mu3 2 2 (⟨(87 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 84596576188481519544086098877434000000000000000000000000 := by
  decide +kernel

theorem cb87_0_3_1 :
    ((∑ w, mu3 2 2 (⟨(87 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(87 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((84596576188481519544086098877434000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![0,3,1], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 84596576188481519544086098877434000000000000000000000000 cm87_0_3_1) (le_of_eq ?_)
  push_cast
  ring

theorem cm87_0_4_0 :
    ∑ w, mu3 2 2 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w = 25074871983320512306913901122566000000000000000000000000 := by
  decide +kernel

theorem cb87_0_4_0 :
    ((∑ w, mu3 2 2 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2))) w : ℚ) : ℝ)) ≤
      ((25074871983320512306913901122566000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstepC (87 : Fin 88) (⟨![0,4,0], by decide +kernel⟩) (Or.inl rfl)
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25074871983320512306913901122566000000000000000000000000 cm87_0_4_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_0 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 84596576188481519544086098877434000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 0 then mu3 2 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (0 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_0 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((84596576188481519544086098877434000000000000000000000000 * 7 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (0 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((7 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 84596576188481519544086098877434000000000000000000000000 gm87_0) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_1 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 25074871983320512306913901122566000000000000000000000000 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 1 then mu3 2 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (1 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gb87_1 :
    ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℕ) : ℝ) *
        entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1)))) w : ℚ) : ℝ)) ≤
      ((25074871983320512306913901122566000000000000000000000000 * 693147180559945309417233000006 : ℕ) : ℝ)/10^30 := by
  refine le_trans (kstep (Sum.inr ((87 : Fin 88), (1 : Fin (2 * 2 ^ (2 - 1) + 1))))
    (fun (v : CompleteSplit.CompleteWord 2) (k : Fin 4) => if 3 * (v 0).val + (v 1).val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if 3 * (v 0).val + (v 1).val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (-100 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0)) ((693147180559945309417233000006 : ℚ)/10^30) mme_released_recursive_level3_compat36.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 25074871983320512306913901122566000000000000000000000000 gm87_1) (le_of_eq ?_)
  push_cast
  ring

theorem gm87_2 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (2 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 2 then mu3 2 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (2 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_3 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (3 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 3 then mu3 2 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (3 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem gm87_4 :
    ∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w = 0 := by
  have hp : ∀ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), (4 : Fin (2 * 2 ^ (2 - 1) + 1)))) w =
      ∑ c : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
        if ¬ ((c.val 0).val = 0 ∨ (c.val 1).val = 0) ∧ (c.val 2).val = 4 then mu3 2 2 ⟨(87 : Fin 88), c⟩ w else 0 :=
    fun w ↦ hgrp2 (87 : Fin 88) (4 : Fin (2 * 2 ^ (2 - 1) + 1)) w
  simp only [hp]
  decide +kernel

theorem reg87 :
    ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 (87 : Fin 88)),
            if yzBoundary 1 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr ((87 : Fin 88), j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr ((87 : Fin 88), j)) w : ℚ) : ℝ))) ≤
      ((76018455088210746876586551328127242940521709414063000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [hsp87 (fun b ↦
    if yzBoundary 1 (⟨(87 : Fin 88), b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
      ((∑ w, mu3 2 2 ⟨(87 : Fin 88), b⟩ w : ℕ) : ℝ) *
        entropy (fun w ↦ ((normQ (mu3 2 2 ⟨(87 : Fin 88), b⟩) w : ℚ) : ℝ))
    else 0)]
  rw [if_pos (show yzBoundary 1 (⟨(87 : Fin 88), (⟨![0,3,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_pos (show yzBoundary 1 (⟨(87 : Fin 88), (⟨![0,4,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from Or.inl rfl)]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(87 : Fin 88), (⟨![1,2,1], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [if_neg (show ¬ yzBoundary 1 (⟨(87 : Fin 88), (⟨![1,3,0], by decide +kernel⟩)⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) from by simp [yzBoundary, yBoundary, zBoundary])]
  rw [hJ87]
  rw [kzero _ gm87_2]
  rw [kzero _ gm87_3]
  rw [kzero _ gm87_4]
  refine le_trans (le_of_eq (by ring)) (le_trans (add_le_add cb87_0_3_1 (add_le_add cb87_0_4_0 (add_le_add gb87_0 gb87_1))) (le_of_eq (by push_cast; ring)))

end L3K

theorem solution :
    ∑ a ∈ (({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 2 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 2)) then
              ((∑ w, mu3 2 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 2 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 2 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((203696259401120877076961512667146235569596511422240500769848766862000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg66 (add_le_add L3K.reg67 (add_le_add L3K.reg68 (add_le_add L3K.reg69 (add_le_add L3K.reg70 (add_le_add L3K.reg71 (add_le_add L3K.reg72 (add_le_add L3K.reg73 (add_le_add L3K.reg74 (add_le_add L3K.reg75 (add_le_add L3K.reg76 (add_le_add L3K.reg77 (add_le_add L3K.reg78 (add_le_add L3K.reg79 (add_le_add L3K.reg80 (add_le_add L3K.reg81 (add_le_add L3K.reg82 (add_le_add L3K.reg83 (add_le_add L3K.reg84 (add_le_add L3K.reg85 (add_le_add L3K.reg86 L3K.reg87))))))))))))))))))))) (le_of_eq (by push_cast; ring))
