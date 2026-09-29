-- Prove2me | Theorems.Thm_mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
-- name    : mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:38:22.150038+00:00
-- url     : https://prove2.me/theorems/d181bb83-a71e-412a-a9c8-1e15e9e06cfc
-- title:
--   One zero selected coordinate kills a complete Kronecker basis word
-- statement:
--   For an ordered Kronecker product equipped coordinatewise with finite bases, choose one basis label in every mode and coordinate. If the three-mode singleton projection kills one coordinate tensor, then the singleton projection onto the complete product-basis word kills the full Kronecker product, even after arbitrary mode-wise linear postmaps.
-- source:
--   Standard tensor-product basis recursion and functoriality of PiTensorProduct.map.

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Module TensorProduct

universe u

set_option autoImplicit false

open MME

theorem mme_kronFin_selected_basis_postmap_eq_zero_of_coordinate
    {K : Type u} [Field K] {d n : ℕ}
    (X : Fin n → TensorObj K d)
    {Index : Fin n → Fin d → Type u}
    [∀ r i, Fintype (Index r i)]
    [∀ r i, DecidableEq (Index r i)]
    (b : ∀ r i, Basis (Index r i) K ((X r).V i))
    (word : ∀ i r, Index r i)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i, (TensorObj.kronFin n X).V i →ₗ[K] W i)
    (r : Fin n)
    (hlocal : PiTensorProduct.map
      (fun i ↦ MME.DWZComponentRestriction.basisLabelProjection
        (b r i) id {word i r}) (X r).t = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (TensorObj.kronFinModePiBasis n X i (fun r ↦ b r i))
            id {word i}))
        (TensorObj.kronFin n X).t = 0 := by
  sorry
