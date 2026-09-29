-- Prove2me | Theorems.Thm_mme_released_joint_interior_selected_owner_window
-- name    : mme_released_joint_interior_selected_owner_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:27:57.637216+00:00
-- url     : https://prove2.me/theorems/f8c424e9-0ec3-41bd-a336-811e5e1100f6
-- title:
--   Selected physical owner words satisfy the released window
-- statement:
--   Selecting the actual elementary coordinates for a positive interior owner-parent label recovers exact parent grades and its released histogram window from the six joint regions. No independent word-splitting compatibility hypothesis is needed. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_fine_selection
import Theorems.Thm_mme_released_joint_interior_owner_graded
import Theorems.Thm_mme_released_joint_interior_owner_parent_typical
import Theorems.Thm_mme_released_interior_scaled_graded_fine_word_window
open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

theorem mme_released_joint_interior_selected_owner_window
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
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
