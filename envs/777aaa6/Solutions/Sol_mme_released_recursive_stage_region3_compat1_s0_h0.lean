-- Prove2me | solution 1 for mme_released_recursive_stage_region3_compat1_s0_h0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T11:59:20.086983+00:00
-- url     : https://prove2.me/submissions/8455a489-8513-46ba-9a22-7719cd4cdc73

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

end L3K

theorem solution :
    ∑ a ∈ (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 3 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 3)) then
              ((∑ w, mu3 3 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 3 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 3 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((190170199673334995551562514510317725046730283532815312945751107604000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  refine le_trans (add_le_add L3K.reg0 (add_le_add L3K.reg1 (add_le_add L3K.reg2 (add_le_add L3K.reg3 (add_le_add L3K.reg4 (add_le_add L3K.reg5 (add_le_add L3K.reg6 (add_le_add L3K.reg7 (add_le_add L3K.reg8 (add_le_add L3K.reg9 (add_le_add L3K.reg10 (add_le_add L3K.reg11 (add_le_add L3K.reg12 (add_le_add L3K.reg13 (add_le_add L3K.reg14 (add_le_add L3K.reg15 (add_le_add L3K.reg16 (add_le_add L3K.reg17 (add_le_add L3K.reg18 (add_le_add L3K.reg19 (add_le_add L3K.reg20 L3K.reg21))))))))))))))))))))) (le_of_eq (by push_cast; ring))
