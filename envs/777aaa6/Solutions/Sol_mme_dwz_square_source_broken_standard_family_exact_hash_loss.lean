-- Prove2me | solution 1 for mme_dwz_square_source_broken_standard_family_exact_hash_loss
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:23:30.99603+00:00
-- url     : https://prove2.me/submissions/8e56f2f8-4b50-4ee5-a328-554bfc6a8514
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
import Theorems.Thm_mme_complete_group_prefix_selection_restrict

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
      ∃ (k p : ℕ)
          (copies : Fin (k * g) → BrokenBlockCopy (DWZStandardBlock m)),
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
          let G : Fin (k * g) → D.X.TypeGrading 2 := fun r ↦
            D.X.basisZAllowedGrading D.basis
              (fun W ↦ D.label W ∈ (copies r).nonholes)
          TensorObj.Restrict
            (TensorObj.bigAdd (fun r ↦
              (G r).blockSubtensor (fun _ ↦ 0)))
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L)) ∧
        Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              (Dhash * (16 * (((4 * L + 1 : ℕ) : ℝ))))) ≤
          (k : ℝ) := by
  filter_upwards
      [mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
        (K := K)] with m hm
  dsimp only at hm
  obtain ⟨n, p, copies, hmpos, hp, hpUpper, hseven, hsource,
    hlarge, hlower⟩ := hm
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let g : ℕ := 8 * (4 * L + 1)
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
  let D : DWZStandardLabelledData K m :=
    { X := TensorObj.kronFin 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
        (fun r ↦ restrictedComponentZBasis K r m)
      label := groupedUsefulBlock m }
  let X : BrokenBlockCopy (DWZStandardBlock m) → TensorObj K 3 := fun copy ↦
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    G.blockSubtensor (fun _ ↦ 0)
  have hg : 0 < g := by
    dsimp only [g]
    positivity
  have hselected :=
    mme_complete_group_prefix_selection_restrict
      (K := K) (d := 3) (hd := by norm_num) g hg copies
      (fun copy ↦
        7 * Fintype.card (DWZStandardBlock m) ≤
          8 * copy.nonholes.card)
      hseven X
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L)
      (by simpa only [X, D, L] using hsource)
      A (by simpa only [A, g, Dhash, jointPoly, degreePoly, zPoly,
        compatibilityPoly, x, L] using hlarge)
      (by simpa only [A, Dhash, jointPoly, degreePoly, zPoly,
        compatibilityPoly, x, L] using hlower)
  obtain ⟨k, selected, hselectedSeven, hselectedSource,
    hselectedCount⟩ := hselected
  refine ⟨k, p, selected, hmpos, hp, ?_, hselectedSeven, ?_, ?_⟩
  · simpa only [L] using hpUpper
  · simpa only [X, D] using hselectedSource
  · have hdenom :
        A / (2 * (g : ℝ)) =
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              (Dhash * (16 * (((4 * L + 1 : ℕ) : ℝ))))) := by
        let B : ℝ := Real.rpow 2 (retainedLogRate * (L : ℝ))
        let q : ℝ :=
          (((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp
              (-4 * Real.sqrt (Real.log (((p / 2 : ℕ) : ℝ))))
        have htwoG :
            2 * (g : ℝ) = 16 * (((4 * L + 1 : ℕ) : ℝ)) := by
          dsimp only [g]
          push_cast
          ring
        change (B * (q / Dhash)) / (2 * (g : ℝ)) =
          B * (q / (Dhash * (16 * (((4 * L + 1 : ℕ) : ℝ)))))
        rw [mul_div_assoc', div_div, htwoG, ← mul_div_assoc']
    rw [← hdenom]
    exact hselectedCount
