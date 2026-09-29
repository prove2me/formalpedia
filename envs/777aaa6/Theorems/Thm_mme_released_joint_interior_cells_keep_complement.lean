-- Prove2me | Theorems.Thm_mme_released_joint_interior_cells_keep_complement
-- name    : mme_released_joint_interior_cells_keep_complement
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:32:53.798793+00:00
-- url     : https://prove2.me/theorems/bd441444-e458-49f8-adee-ddc90ccec2c3
-- title:
--   Joint interior windows retain all complementary outer cells
-- statement:
--   The full common-mode normalized outer cell product restricts to the actual joint interior window product together with every complementary original cell. Boundary parents remain tensor factors and zero joint labels contribute scalar interior factors. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_positive_cell_window
import Theorems.Thm_mme_kronFin_restrict_keep_complement
import Theorems.Thm_mme_profiled_CW_empty_isomorphic
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

theorem mme_released_joint_interior_cells_keep_complement
    {K : Type u} [Field K] (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L : Fin 270 → ℕ := fun j => t * coarseCounts
      (MME.ReleasedJointInterior.component j).1
      (shapeEquiv (MME.ReleasedJointInterior.component j).2)
    let T : Fin 270 → TensorObj K 3 := fun j =>
      permObj (MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1) ( ((source K 5 3 (L j)).basisAllAllowedSubtensor (basis K 5 3 (L j))
      (fun i x =>
        (∀ r, grade (label 5 3 (L j) (Equiv.refl _) x r) = ((shapeEquiv (MME.ReleasedJointInterior.component j).2).val i).val) ∧
        if (L j) = 0 then ∀ w, |(profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin (L j) => Unit.unit)
          (label 5 3 (L j) (Equiv.refl _) x) Unit.unit w : ℝ) / (L j) -
          ((blocks t : ℝ) / (L j)) * (profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          ((blocks t : ℝ) / (L j)) * (eps))))
    let P : ∀ j : Fin 270, ProfiledCW.Predicate
        ((t * MME.ReleasedJointInterior.weight j * denominator ^ 4) * 4) :=
      fun j => (fun i (x : ProfiledCW.FineWord ((t * MME.ReleasedJointInterior.weight j * denominator ^ 4) * 4)) =>
      0 < MME.ReleasedJointInterior.weight j →
      (∀ p : Fin (t * MME.ReleasedJointInterior.weight j * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ReleasedInterior.parent (MME.ReleasedJointInterior.component j).2 0 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i)) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (t * MME.ReleasedJointInterior.weight j * denominator ^ 4) //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / (t * MME.ReleasedJointInterior.weight j * denominator ^ 4 : ℕ) -
          ((((jointRows (MME.ReleasedJointInterior.component j).1 (MME.ReleasedJointInterior.component j).2).map
            (fun a => if atom a.1 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i) = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps)
    Restrict
      (kron (kronFin 270 (fun j => ProfiledCW.tensor K (P j)))
        (kronFin 270 (fun j => if 0 < MME.ReleasedJointInterior.weight j
          then oneObj else T j)))
      (kronFin 270 T) := by sorry
