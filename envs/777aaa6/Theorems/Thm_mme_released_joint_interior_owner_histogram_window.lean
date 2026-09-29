-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_histogram_window
-- name    : mme_released_joint_interior_owner_histogram_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:28:01.735765+00:00
-- url     : https://prove2.me/theorems/8f6d620a-1953-4ef3-8585-bd051d207648
-- title:
--   Joint windows recover the released owner histogram
-- statement:
--   For positive interior parent mass, the common joint windows imply the released full-word histogram window under an explicit position equivalence and physical splitting compatibility. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_owner_parent_typical
import Theorems.Thm_mme_released_interior_scaled_partition_parent_window
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

theorem mme_released_joint_interior_owner_histogram_window
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
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
