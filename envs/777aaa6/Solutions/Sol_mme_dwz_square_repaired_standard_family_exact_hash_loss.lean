-- Prove2me | solution 1 for mme_dwz_square_repaired_standard_family_exact_hash_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:15:39.257696+00:00
-- url     : https://prove2.me/submissions/52fd0d90-b01b-4979-967d-8875074a4b7f

import Theorems.Thm_mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
import Theorems.Thm_mme_dwz_source_broken_family_transport_preserves_nonholeFraction
import Theorems.Thm_mme_dwz_greedy_item_grouping
import Theorems.Thm_mme_dwz_flat_aggregate_groups_restrict_standard
import Theorems.Thm_mme_dwz_aggregate_group_count_choice
import Theorems.Thm_mme_dwz_table2_exact_hash_lower_eventually_two_groups
import Theorems.Thm_mme_dwz_table2_standard_block_card_le_two_pow_four_length
import Theorems.Thm_mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

theorem solution
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
      ∃ (k p : ℕ) (D : ℝ),
        2 ≤ p ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
        0 < D ∧
        D ≤ Real.exp (B * Real.sqrt (((L + 1 : ℕ) : ℝ))) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun _ : Fin k => dwzTable2StandardObj K m))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              D) ≤
          (k : ℝ) := by
  have hscale :
      Tendsto
        (fun m : ℕ ↦ MME.DWZTable2Counts.scale * m)
        atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop
        (by norm_num [MME.DWZTable2Counts.scale] :
          0 < MME.DWZTable2Counts.scale))
  have hlarge := hscale.eventually
    mme_dwz_table2_exact_hash_lower_eventually_two_groups
  filter_upwards
      [mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
        (K := K), hlarge] with m hm hlargeM
  dsimp only at hm hlargeM ⊢
  obtain ⟨n, p, outer, sourceCopy, hmpos, hp, hpUpper, houter,
    hsource, hmass⟩ := hm
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let H : ℕ := 4 * L + 1
  let x : ℝ := (((L + 1 : ℕ) : ℝ))
  let jointPoly : ℝ := (6 * x) ^ 15
  let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
  let zPoly : ℝ := (6 * x) ^ 5
  let compatibilityPoly : ℝ := (6 * x) ^ 9
  let Dhash : ℝ :=
    32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
  let A : ℝ :=
    Real.rpow 2 (retainedLogRate * (L : ℝ)) *
      (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp
            (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ))))) /
        Dhash)
  let Dloss : ℝ := Dhash * (16 * (H : ℝ))
  let S : TensorObj K 3 :=
    (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
  obtain ⟨standardCopy, hFraction, hstandardSource⟩ :=
    mme_dwz_source_broken_family_transport_preserves_nonholeFraction
      S outer houter hmpos sourceCopy (by simpa only [S, L] using hsource)
  have hmassStandard : A ≤ ∑ r, nonholeFraction (standardCopy r) := by
    simpa only [A, Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x, L, hFraction] using hmass
  let items : List (BrokenBlockCopy (DWZStandardBlock m)) :=
    List.ofFn standardCopy
  have hitemsSum :
      (items.map nonholeFraction).sum =
        ∑ r, nonholeFraction (standardCopy r) := by
    simp only [items, List.map_ofFn, ← List.sum_ofFn]
    rfl
  have hweightNonneg : ∀ copy ∈ items, 0 ≤ nonholeFraction copy := by
    intro copy _hcopy
    unfold nonholeFraction
    positivity
  have hweightOne : ∀ copy ∈ items, nonholeFraction copy ≤ 1 := by
    intro copy _hcopy
    unfold nonholeFraction
    by_cases hcardZero : Fintype.card (DWZStandardBlock m) = 0
    · rw [hcardZero]
      norm_num
    · apply (div_le_one (by
          exact_mod_cast Nat.pos_of_ne_zero hcardZero)).2
      exact_mod_cast copy.nonholes.card_le_univ
  have hH : 1 ≤ H := by
    dsimp only [H]
    omega
  have hlargeA : 16 * (H : ℝ) ≤ A := by
    have h := hlargeM p hp hpUpper
    dsimp only [A, Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x, H, L] at h ⊢
    push_cast at h ⊢
    linarith
  have hmassA : A ≤ (items.map nonholeFraction).sum := by
    rw [hitemsSum]
    exact hmassStandard
  obtain ⟨q, hqLower, hqBudget⟩ :=
    mme_dwz_aggregate_group_count_choice H (by omega) A
      (items.map nonholeFraction).sum hlargeA hmassA
  obtain ⟨groups, remainder, hsplit, hgroupsLength, hgroups⟩ :=
    mme_dwz_greedy_item_grouping nonholeFraction items
      hweightNonneg hweightOne (H : ℝ) (by positivity) q
      (by simpa only [Nat.cast_add, Nat.cast_one] using hqBudget)
  have hcard := mme_dwz_table2_standard_block_card_le_two_pow_four_length m
  have hrepair := mme_dwz_flat_aggregate_groups_restrict_standard
    K m 4 L (by norm_num) (by
      dsimp only [L]
      exact Nat.mul_pos (by
        norm_num [MME.DWZTable2Counts.scale]) hmpos)
    groups remainder (by simpa only using hcard)
    (by
      intro group hgroup
      have hg := (hgroups group hgroup).1
      simpa only [H] using hg)
  have hitemsSource :
      let D : DWZStandardLabelledData K m :=
        { X := TensorObj.kronFin 15
            (fun r : Fin 15 ↦ restrictedComponentPower K r m)
          basis := TensorObj.kronFinModePiBasis 15
            (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
            (fun r ↦ restrictedComponentZBasis K r m)
          label := groupedUsefulBlock m }
      let G : BrokenBlockCopy (DWZStandardBlock m) → D.X.TypeGrading 2 :=
        fun copy ↦ D.X.basisZAllowedGrading D.basis
          (fun W ↦ D.label W ∈ copy.nonholes)
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r : Fin items.length ↦
          (G (items.get r)).blockSubtensor (fun _ ↦ 0))) S := by
    dsimp only at hstandardSource ⊢
    let Xcopy : BrokenBlockCopy (DWZStandardBlock m) → TensorObj K 3 :=
      fun copy ↦
        ((TensorObj.kronFin 15
            (fun s : Fin 15 ↦ restrictedComponentPower K s m)).basisZAllowedGrading
          (TensorObj.kronFinModePiBasis 15
            (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
            (fun s ↦ restrictedComponentZBasis K s m))
          (fun W ↦ groupedUsefulBlock m W ∈ copy.nonholes)).blockSubtensor
            (fun _ ↦ 0)
    have hitemsIso : TensorObj.Isomorphic
        (TensorObj.bigAdd (fun r : Fin items.length ↦
          Xcopy (items.get r)))
        (TensorObj.bigAdd (fun r : Fin n ↦ Xcopy (standardCopy r))) := by
      apply TensorQ.toQ_eq_iff.mp
      rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
      rw [← List.sum_ofFn, ← List.sum_ofFn]
      simp [items]
    have hstandardSource' : TensorObj.Restrict
        (TensorObj.bigAdd (fun r : Fin n ↦ Xcopy (standardCopy r))) S := by
      simpa only [Xcopy] using hstandardSource
    simpa only [Xcopy] using
      TensorObj.Restrict.trans hitemsIso.1 hstandardSource'
  rw [hsplit] at hitemsSource
  rw [hgroupsLength] at hrepair
  dsimp only at hrepair hitemsSource
  have hfinalRestrict := TensorObj.Restrict.trans hrepair hitemsSource
  refine ⟨q, p, Dloss, hp, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [L] using hpUpper
  · dsimp only [Dloss, Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x, H]
    positivity
  · simpa only [Dloss, Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x, H, L] using
      mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt L
  · simpa only [S, L] using hfinalRestrict
  · have hdenom :
        A / (16 * (H : ℝ)) =
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dloss) := by
        let R : ℝ := Real.rpow 2 (retainedLogRate * (L : ℝ))
        let b : ℝ :=
          (((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp
              (-4 * Real.sqrt (Real.log (((p / 2 : ℕ) : ℝ))))
        change (R * (b / Dhash)) / (16 * (H : ℝ)) =
          R * (b / (Dhash * (16 * (H : ℝ))))
        rw [mul_div_assoc', div_div, ← mul_div_assoc']
    rw [← hdenom]
    simpa only [L] using hqLower
