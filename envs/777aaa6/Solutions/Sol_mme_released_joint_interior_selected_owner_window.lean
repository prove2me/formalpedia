-- Prove2me | solution 1 for mme_released_joint_interior_selected_owner_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:31:23.892982+00:00
-- url     : https://prove2.me/submissions/8bead6d2-3116-4261-985d-72c1d9b8ab6a

import Theorems.Thm_mme_released_joint_interior_fine_selection
import Theorems.Thm_mme_released_joint_interior_owner_graded
import Theorems.Thm_mme_released_joint_interior_owner_parent_typical
import Theorems.Thm_mme_released_interior_scaled_graded_fine_word_window

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- Selecting the actual elementary coordinates of an owner-parent label
recovers its graded released histogram window from the six joint regions.
No additional word-splitting compatibility is assumed. -/
theorem solution
    (k : ℕ) (hk : 0 < k) (j : Fin 270) (hw : 0 < weight j)
    (hi : (ReleasedInterior.seed (component j).1 (component j).2).boundary = []) :
    ∃ e : Fin ((k * weight j * denominator ^ 4) * 2) ≃
        Position (fun r => size r k j),
      ∀ (i : Fin 3) (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
        (x : ∀ r : Fin 6, Fin 3 → ProfiledCW.FineWord (blocks r k * 4)) (eps : ℝ),
        (∀ r : Fin 6,
          Graded (parent_total r) ((orientation (component j).1 r).symm i) (a r)
            (ProfiledCW.split (positions r k) (positions_length r k)
              (x r ((orientation (component j).1 r).symm i)))) →
        (∀ r : Fin 6,
          source r k eps ((orientation (component j).1 r).symm i)
            (x r ((orientation (component j).1 r).symm i))) →
        let length : ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * weight j * denominator ^ 4) * 4 := by omega
        let z := fun q =>
          let t := ownerFineEmbedding k j e length q
          x t.1 ((orientation (component j).1 t.1).symm i) t.2
        (∀ p : Fin (k * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  obtain ⟨e, hwindow⟩ := mme_released_interior_scaled_graded_fine_word_window
    (component j).1 (component j).2 hi (k * weight j) (Nat.mul_pos hk hw)
  refine ⟨e, ?_⟩
  intro i a x eps hg ht
  let y := fun r => x r ((orientation (component j).1 r).symm i)
  let f := fun r => ProfiledCW.split (positions r k) (positions_length r k) (y r)
  have hgrade := mme_released_joint_interior_owner_graded k j i a f hg
  have htyp := mme_released_joint_interior_owner_parent_typical k j i eps f ht
  have hsplit := funext (mme_released_joint_interior_fine_selection k j e
    (show ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
      (k * weight j * denominator ^ 4) * 4 by omega) y)
  rw [← hsplit] at hgrade
  have htyp' := (congrArg
    (parentTypical (ReleasedInterior.parent_total (component j).2)
      (fun r => k * weight j * ReleasedInterior.regionalSize
        (component j).1 (component j).2 r)
      (fun r c => k * weight j * ReleasedInterior.splitCount
        (component j).1 (component j).2 r c)
      (fun c w => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2 i c w) eps) hsplit).mpr htyp
  exact hwindow i (fun r t => (splitEquiv r j).symm (a r j t)) _ eps hgrade htyp' 


#print axioms solution
