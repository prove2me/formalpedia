-- Prove2me | solution 1 for mme_kronFin_family_mode_map_selected_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:26:30.328349+00:00
-- url     : https://prove2.me/submissions/1458331b-f56a-4408-90ef-989a8f1a596c

import Definitions.Def_mme_kronFin_family_mode_map_basis_data

open MME Module TensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.TensorObj

private theorem kronFinModePiBasis_succ_apply_selected
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, index r) :
    TensorObj.kronFinModePiBasis (n + 1) T i b w =
      b 0 (w 0) ⊗ₜ[K]
        TensorObj.kronFinModePiBasis n
          (fun r : Fin n ↦ T r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ w r.succ) := by
  change (((b 0).tensorProduct
    (TensorObj.kronFinModePiBasis n
      (fun r : Fin n ↦ T r.succ) i
      (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) w = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

/-- Exact factorwise images for one selected dependent product-basis word
assemble to the exact image of the full finite Kronecker basis word. -/
theorem kronFinFamilyModeMap_selected_basis
    {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → TensorObj K d) (i : Fin d)
    {indexX indexY : Fin n → Type u}
    (bX : ∀ r, Basis (indexX r) K ((X r).V i))
    (bY : ∀ r, Basis (indexY r) K ((Y r).V i))
    (f : ∀ r j, (X r).V j →ₗ[K] (Y r).V j)
    (wX : ∀ r, indexX r) (wY : ∀ r, indexY r)
    (hf : ∀ r, f r i (bX r (wX r)) = bY r (wY r)) :
    kronFinFamilyModeMap n X Y f i
        (TensorObj.kronFinModePiBasis n X i bX wX) =
      TensorObj.kronFinModePiBasis n Y i bY wY := by
  induction n with
  | zero =>
      letI : Unique (∀ r : Fin 0, indexX r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      letI : Unique (∀ r : Fin 0, indexY r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      simp only [kronFinFamilyModeMap, TensorObj.kronFinModePiBasis]
      calc
        _ = (1 : K) := Module.Basis.singleton_apply _ K wX
        _ = _ := (Module.Basis.singleton_apply _ K wY).symm
  | succ n ih =>
      rw [kronFinModePiBasis_succ_apply_selected,
        kronFinModePiBasis_succ_apply_selected]
      change TensorProduct.map (f 0 i)
          (kronFinFamilyModeMap n
            (fun r : Fin n ↦ X r.succ)
            (fun r : Fin n ↦ Y r.succ)
            (fun r j ↦ f r.succ j) i)
          (bX 0 (wX 0) ⊗ₜ[K]
            TensorObj.kronFinModePiBasis n
              (fun r : Fin n ↦ X r.succ) i
              (fun r ↦ bX r.succ) (fun r ↦ wX r.succ)) = _
      rw [TensorProduct.map_tmul, hf 0]
      rw [ih (fun r : Fin n ↦ X r.succ)
        (fun r : Fin n ↦ Y r.succ)
        (fun r ↦ bX r.succ) (fun r ↦ bY r.succ)
        (fun r j ↦ f r.succ j)
        (fun r ↦ wX r.succ) (fun r ↦ wY r.succ)
        (fun r ↦ hf r.succ)]

end MME.TensorObj

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → MME.TensorObj K d) (i : Fin d)
    {indexX indexY : Fin n → Type u}
    (bX : ∀ r, Basis (indexX r) K ((X r).V i))
    (bY : ∀ r, Basis (indexY r) K ((Y r).V i))
    (f : ∀ r j, (X r).V j →ₗ[K] (Y r).V j)
    (wX : ∀ r, indexX r) (wY : ∀ r, indexY r)
    (hf : ∀ r, f r i (bX r (wX r)) = bY r (wY r)) :
    MME.TensorObj.kronFinFamilyModeMap n X Y f i
        (MME.TensorObj.kronFinModePiBasis n X i bX wX) =
      MME.TensorObj.kronFinModePiBasis n Y i bY wY := by
  exact MME.TensorObj.kronFinFamilyModeMap_selected_basis
    X Y i bX bY f wX wY hf
