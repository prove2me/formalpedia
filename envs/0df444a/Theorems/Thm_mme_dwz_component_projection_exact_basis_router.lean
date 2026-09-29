-- Prove2me | Theorems.Thm_mme_dwz_component_projection_exact_basis_router
-- name    : mme_dwz_component_projection_exact_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T21:02:45.419551+00:00
-- url     : https://prove2.me/theorems/fbd8f490-6518-4d3d-b8df-a6e4a14c4027
-- title:
--   Exact basis router for each restricted DWZ component power
-- statement:
--   Fix one of the fifteen Table-2 components and its prescribed power. There are modewise linear maps from the unrestricted component power to its available-word restriction such that
--
--   $$
--   (\bigotimes_i f_i)(T_s^{\otimes c_s m})=T_{s,\mathrm{allowed}}.
--   $$
--
--   On the canonical Z product basis, every word satisfying the exact Table-2 availability histogram is sent to the corresponding literal basis vector of the restricted component power, while every word that fails that histogram is sent to zero. This is the local projection-and-zeroing certificate needed to regroup retained source positions into the fifteen component powers without losing coordinate semantics.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (restriction to the prescribed component-word histograms); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_TypeGrading_kron

open MME PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_dwz_component_projection_exact_basis_router
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    ∃ f : ∀ i : Fin 3,
        (((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
          (MME.DWZTable2Counts.component s * m)).V i) →ₗ[K]
          ((MME.DWZComponentRestriction.restrictedComponentPower K s m).V i),
      PiTensorProduct.map f
          ((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
            (MME.DWZTable2Counts.component s * m)).t =
        (MME.DWZComponentRestriction.restrictedComponentPower K s m).t ∧
      (∀ (w : MME.DWZComponentRestriction.PowIndex
          (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
            (MME.DWZSquare.shapeZ s))
          (MME.DWZTable2Counts.component s * m))
          (hw : MME.DWZComponentRestriction.componentWordAllowed s m w),
        f 2 (MME.DWZComponentRestriction.componentPowerZBasis K s m w) =
          MME.DWZComponentRestriction.restrictedComponentZBasis K s m
            ⟨w, hw⟩) ∧
      ∀ (w : MME.DWZComponentRestriction.PowIndex
          (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
            (MME.DWZSquare.shapeZ s))
          (MME.DWZTable2Counts.component s * m)),
        ¬ MME.DWZComponentRestriction.componentWordAllowed s m w →
          f 2 (MME.DWZComponentRestriction.componentPowerZBasis K s m w) = 0 := by
  sorry
