-- Prove2me | solution 1 for mme_released_joint_interior_owner_histogram_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:31:23.283444+00:00
-- url     : https://prove2.me/submissions/287ebfd3-ea28-4523-8242-eb201c07fa0c

import Theorems.Thm_mme_released_joint_interior_owner_parent_typical
import Theorems.Thm_mme_released_interior_scaled_partition_parent_window

open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- A positive interior parent recovers its released full-word histogram from
the common joint windows. The position equivalence and splitting compatibility
keep the reconstructed parent words tied to the actual physical child words. -/
theorem solution
    (k : ℕ) (hk : 0 < k) (j : Fin 270) (hw : 0 < weight j)
    (hi : (ReleasedInterior.seed (component j).1 (component j).2).boundary = []) :
    ∃ positions : (Σ r : Fin 6, Fin (size r k j)) ≃
        Fin (k * weight j * denominator ^ 4),
      ∀ (i : Fin 3) (g : Fin (k * weight j * denominator ^ 4) → CompleteWord 3)
        (eps : ℝ) (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2),
        (∀ (r : Fin 6) (t : Fin (size r k j)) (h : Fin 2),
          f r ⟨j,t,h⟩ =
            (let v := completeWordSplitEquiv 2 (by decide) (g (positions ⟨r,t⟩))
            ![v.1,v.2] h)) →
        (∀ r : Fin 6,
          parentTypical (parent_total r) (size r k) (splitCount r k)
            (integerProfile r k ((orientation (component j).1 r).symm i)) eps (f r)) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) // g p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  obtain ⟨positions, hwindow⟩ := mme_released_interior_scaled_partition_parent_window
    (component j).1 (component j).2 hi (k * weight j) (Nat.mul_pos hk hw)
  refine ⟨positions, ?_⟩
  intro i g eps f hsplit ht w
  apply hwindow i g eps _ w
  have h := mme_released_joint_interior_owner_parent_typical k j i eps f ht
  have heq : (fun p : Position (fun r => k * weight j *
        ReleasedInterior.regionalSize (component j).1 (component j).2 r) =>
      f p.1 ⟨j,p.2⟩) =
      (fun p =>
        let v := completeWordSplitEquiv 2 (by decide) (g (positions ⟨p.1,p.2.1⟩))
        ![v.1,v.2] p.2.2) := by
    funext p
    exact hsplit p.1 p.2.1 p.2.2
  rw [heq] at h
  exact h


#print axioms solution
