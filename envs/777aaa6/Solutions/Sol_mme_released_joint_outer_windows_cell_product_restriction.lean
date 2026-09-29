-- Prove2me | solution 1 for mme_released_joint_outer_windows_cell_product_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:24.291358+00:00
-- url     : https://prove2.me/submissions/e93feaa9-b964-4c37-a9e0-5e8e39021643

import Theorems.Thm_mme_released_global_normalized_cell_product_restriction
import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_released_joint_interior_profiles

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit MME.TensorObj
universe u
set_option autoImplicit false

private theorem permuted_finite_product {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (kronFin n (fun j => permObj sigma (T j))) (permObj sigma (kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, ← TensorQ.permAut_toQ, map_prod]

/-- The six actual outer histogram windows supply all 270 normalized cells
in the joint mode order. Only whole-owner permutations and product regrouping
are used; the reference addresses and histogram tolerance stay unchanged. -/
theorem solution
    {K : Type u} [Field K] (t : ℕ) (ht : 0 < t)
    (a : ∀ owner : Fin 6, Reference owner t) (eps : ℝ) :
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
    Restrict (kronFin 270 T)
      (kronFin 6 (fun owner => permObj (MME.ReleasedJointInterior.roleEquiv owner)
        (ProfiledCW.tensor K ((frame owner t ht (a owner)).window
          (windowGood owner t eps))))) := by
  classical
  intro L T
  let d : Fin 45 ≃ Cell 8 1 (fun _ _ => 8) :=
    { toFun := fun s => ⟨0, shapeEquiv s⟩
      invFun := fun c => shapeEquiv.symm c.2
      left_inv := fun s => shapeEquiv.symm_apply_apply s
      right_inv := by
        rintro ⟨r,c⟩
        have hr : r = 0 := Subsingleton.elim _ _
        subst r
        simp only [Equiv.apply_symm_apply] }
  have howner (owner : Fin 6) :
      Restrict (kronFin 45 (fun s => T (finProdFinEquiv (owner,s))))
        (permObj (MME.ReleasedJointInterior.roleEquiv owner)
          (ProfiledCW.tensor K ((frame owner t ht (a owner)).window
            (windowGood owner t eps)))) := by
    have h := mme_released_global_normalized_cell_product_restriction
      (K := K) owner t ht (a owner) d eps
    have hcomponent (s : Fin 45) :
        MME.ReleasedJointInterior.component (finProdFinEquiv (owner,s)) = (owner,s) :=
      finProdFinEquiv.symm_apply_apply (owner,s)
    let V : Fin 45 → TensorObj K 3 := fun s =>
      let m := t * coarseCounts owner (shapeEquiv s)
      (source K 5 3 m).basisAllAllowedSubtensor (basis K 5 3 m) (fun i x =>
        (∀ r, grade (label 5 3 m (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if m = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤ eps
        else ∀ w, |(count (fun _ : Fin m => Unit.unit)
          (label 5 3 m (Equiv.refl _) x) Unit.unit w : ℝ) / (m : ℝ) -
          ((blocks t : ℝ) / (m : ℝ)) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / (m : ℝ)) * eps)
    have hV : Restrict (kronFin 45 V)
        (ProfiledCW.tensor K ((frame owner t ht (a owner)).window
          (windowGood owner t eps))) := h
    have hp := permuted_finite_product V (MME.ReleasedJointInterior.roleEquiv owner)
    have hr := hp.1.trans (permObj_restrict (MME.ReleasedJointInterior.roleEquiv owner) hV)
    have heq (s : Fin 45) : T (finProdFinEquiv (owner,s)) =
        permObj (MME.ReleasedJointInterior.roleEquiv owner) (V s) := by
      have hL : L (finProdFinEquiv (owner,s)) = t * coarseCounts owner (shapeEquiv s) := by
        simp only [L, hcomponent]
      dsimp only [T]
      rw [hL]
      simp only [hcomponent]
      rfl
    rw [show (fun s => T (finProdFinEquiv (owner,s))) =
      (fun s => permObj (MME.ReleasedJointInterior.roleEquiv owner) (V s)) from funext heq]
    exact hr
  have hflat : Isomorphic (kronFin 270 T)
      (kronFin 6 (fun owner => kronFin 45 (fun s => T (finProdFinEquiv (owner,s))))) := by
    rw [← TensorQ.toQ_eq_iff]
    simp only [mme_toQ_kronFin]
    calc
      _ = ∏ p : Fin 6 × Fin 45, TensorQ.toQ (T (finProdFinEquiv p)) :=
        Fintype.prod_equiv finProdFinEquiv.symm _ _
          (fun j => congrArg (fun x => TensorQ.toQ (T x))
            (finProdFinEquiv.apply_symm_apply j).symm)
      _ = _ := Fintype.prod_prod_type _
  exact hflat.1.trans (mme_kronFin_mono_restrict howner)


#print axioms solution
