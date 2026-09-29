-- Prove2me | Theorems.Thm_mme_released_joint_interior_common_mode_window
-- name    : mme_released_joint_interior_common_mode_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:07:56.764588+00:00
-- url     : https://prove2.me/theorems/75a00f06-a78c-4386-8492-61ae234833e8
-- title:
--   Common joint modes recover every owner window
-- statement:
--   After returning each outer owner to the common source mode order, the same mode in each joint region recovers every positive interior owner-parent histogram window on its actual selected coordinates. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_selected_owner_window
open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

theorem mme_released_joint_interior_common_mode_window
    (k : ℕ) (hk : 0 < k) (j : Fin 270) (hw : 0 < weight j)
    (hi : (ReleasedInterior.seed (component j).1 (component j).2).boundary = []) :
    ∃ e : Fin ((k * weight j * denominator ^ 4) * 2) ≃
        Position (fun r => size r k j),
      ∀ (i : Fin 3) (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
        (x : ∀ r : Fin 6, ProfiledCW.FineWord (blocks r k * 4)) (eps : ℝ),
        (∀ r : Fin 6,
          Graded (parent_total r) ((roleEquiv r).symm i) (a r)
            (ProfiledCW.split (positions r k) (positions_length r k)
              (x r))) →
        (∀ r : Fin 6,
          source r k eps ((roleEquiv r).symm i)
            (x r)) →
        let length : ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * weight j * denominator ^ 4) * 4 := by omega
        let z := fun q =>
          let t := ownerFineEmbedding k j e length q
          x t.1 t.2
        (∀ p : Fin (k * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1 ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps  := by sorry
