-- Prove2me | Theorems.Thm_mme_gradedAddressBlockModeEquiv_comp_proj
-- name    : mme_gradedAddressBlockModeEquiv_comp_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:00:21.81828+00:00
-- url     : https://prove2.me/theorems/df5de222-61a6-4ba7-8f7e-63901ac8a8b0
-- title:
--   Canonical graded-address mode transport cancels projection
-- statement:
--   Let two address families for a tensor power agree in one selected mode. Transporting the graded-address block of the first family through the canonical mode equivalence and then projecting is exactly the same as projecting directly to the second family:
--
--   $$E_i\circ P_{a,i}=P_{a',i}.$$
--
--   This commuting square is the canonical transport needed when three tensor modes are selected from different address owners.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, coordinatewise tensor-power grading; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data

open MME Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_gradedAddressBlockModeEquiv_comp_proj
    {K : Type u} [Field K]
    {t R : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t)
    (address address' : Fin 3 → Fin R → Fin t)
    (i : Fin 3) (hi : address i = address' i) :
    (gradedAddressBlockModeEquiv
      G0 R address address' i hi).toLinearMap.comp
        (gradedAddressProj G0 R address i) =
      gradedAddressProj G0 R address' i := by
  sorry
