-- Prove2me | solution 1 for mme_released_global_common_mode_cell_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:47:42.091464+00:00
-- url     : https://prove2.me/submissions/526ed4ee-0019-4fd5-87ee-be49084f73e3

import Theorems.Thm_mme_released_global_parent_source_restricts_common_window
import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
import Definitions.Def_mme_released_joint_interior_profiles

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

-- Avoid unfolding the released tables merely to check binder names.
set_option linter.constructorNameAsVariable false in
/-- A positive normalized outer cell supplies its histogram window in the
common mode order used by joint hashing. The permutation acts on the entire
cell tensor, preserving its physical positions and tolerance. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L := t * coarseCounts owner (shapeEquiv s)
    let X : TensorObj K 3 := ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * (eps)))
    Restrict
      (ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ReleasedInterior.parent s 0 ((MME.ReleasedJointInterior.roleEquiv owner).symm i)) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 ((MME.ReleasedJointInterior.roleEquiv owner).symm i) = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps))
      (permObj (MME.ReleasedJointInterior.roleEquiv owner) X) := by
  classical
  intro L X
  have h := mme_released_global_parent_source_restricts_common_window
    (K := K) owner s ha0 t ht eps heps
  let W : ProfiledCW.Predicate (L * 4) := fun i x =>
    (∀ p : Fin L,
      (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
        ((shapeEquiv s).val i).val) ∧
    ∀ w : CompleteWord 3,
      |(Fintype.card {p : Fin L //
        ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
        ((((jointRows owner s).map
          (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
          (denominator : ℝ)^4| ≤ eps
  have hp := mme_profiled_CW_all_mode_permutations_iso
    (K := K) W (MME.ReleasedJointInterior.roleEquiv owner)
  exact hp.1.trans (permObj_restrict (MME.ReleasedJointInterior.roleEquiv owner) h)


#print axioms solution
