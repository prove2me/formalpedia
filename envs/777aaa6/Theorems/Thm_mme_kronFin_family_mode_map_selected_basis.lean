-- Prove2me | Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
-- name    : mme_kronFin_family_mode_map_selected_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:21:40.997698+00:00
-- url     : https://prove2.me/theorems/cf12cd80-fee9-4b54-a860-0ea0801af4d3
-- title:
--   Factorwise exact images determine one finite Kronecker basis-word image
-- statement:
--   Consider two ordered families of $n$ tensors, with a modewise linear map between each corresponding pair. Fix one mode and choose product-basis words in the source and target families. If each factor map sends the selected source basis vector exactly to the selected target basis vector, then the tensor product of the factor maps sends the full finite Kronecker product-basis word exactly to the target product-basis word. The index families may depend on the factor position.
-- source:
--   Standard tensor-product basis functoriality; used in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5--6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_family_mode_map_basis_data

open MME Module

universe u

set_option autoImplicit false

theorem mme_kronFin_family_mode_map_selected_basis
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
  sorry
