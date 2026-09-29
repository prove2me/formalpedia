-- Prove2me | solution 1 for mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:11:50.960611+00:00
-- url     : https://prove2.me/submissions/634fa1f0-a8c3-4d22-bc27-204da81484c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_dwz_square_source_broken_standard_family_ungrouped_hash_count
import Theorems.Thm_mme_dwz_table2_exact_hash_lower_eventually_two_groups

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let g : ℕ := 8 * (4 * L + 1)
      let x : ℝ := (((L + 1 : ℕ) : ℝ))
      let jointPoly : ℝ := (6 * x) ^ 15
      let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
      let zPoly : ℝ := (6 * x) ^ 5
      let compatibilityPoly : ℝ := (6 * x) ^ 9
      let Dhash : ℝ :=
        32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
      ∃ (n p : ℕ)
          (copies : Fin n → BrokenBlockCopy (DWZStandardBlock m)),
        let A : ℝ :=
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dhash)
        0 < m ∧
        2 ≤ p ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
        (∀ r,
          7 * Fintype.card (DWZStandardBlock m) ≤
            8 * (copies r).nonholes.card) ∧
        (let D : DWZStandardLabelledData K m :=
            { X := TensorObj.kronFin 15
                (fun r : Fin 15 ↦ restrictedComponentPower K r m)
              basis := TensorObj.kronFinModePiBasis 15
                (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
                (fun r ↦ restrictedComponentZBasis K r m)
              label := groupedUsefulBlock m }
          let G : Fin n → D.X.TypeGrading 2 := fun r ↦
            D.X.basisZAllowedGrading D.basis
              (fun W ↦ D.label W ∈ (copies r).nonholes)
          TensorObj.Restrict
            (TensorObj.bigAdd (fun r ↦
              (G r).blockSubtensor (fun _ ↦ 0)))
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L)) ∧
        2 * (g : ℝ) ≤ A ∧
        A ≤ (n : ℝ) := by
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
      [mme_dwz_square_source_broken_standard_family_ungrouped_hash_count
        (K := K), hlarge] with m hm hlargeM
  dsimp only at hm hlargeM ⊢
  obtain ⟨n, p, copies, hmpos, hp, hpUpper, hseven, hsource,
    hcount⟩ := hm
  refine ⟨n, p, copies, hmpos, hp, hpUpper, hseven, hsource, ?_, hcount⟩
  exact hlargeM p hp hpUpper
