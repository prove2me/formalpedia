-- Prove2me | Theorems.Thm_mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
-- name    : mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:04:05.519288+00:00
-- url     : https://prove2.me/theorems/3648fbb4-3534-4108-973f-d16a5615949d
-- title:
--   Exact Z-basis regrouping of a DWZ source address into the fifteen Table-2 powers
-- statement:
--   Let a retained DWZ source address have $N$ ordered positions, and suppose its Table-2 row map has exactly $c_s m$ positions of row $s$, where $c_s$ is the prescribed Table-2 multiplicity and $m>0$. Then the source positions admit a row-preserving enumeration by the fifteen consecutive row fibers. There are modewise linear maps that carry the literal source tensor to the Kronecker product of the fifteen raw component powers. Moreover, for every canonical source $Z$-basis word, the image is exactly the product-basis word of those powers, and the letter in every grouped position is the original source letter at the corresponding enumerated position. The dependent letter equality is expressed by heterogeneous equality because its type depends on the Table-2 row.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2, Table 2, and the component-word regrouping in Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (MME.DWZSourceAligned.coarseAddressObj K outer).V i →ₗ[K]
            (MME.TensorObj.kronFin 15 (fun s ↦
              (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                (MME.DWZTable2Counts.component s * m))).V i,
        PiTensorProduct.map f
            (MME.DWZSourceAligned.coarseAddressObj K outer).t =
          (MME.TensorObj.kronFin 15 (fun s ↦
            (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
              (MME.DWZTable2Counts.component s * m))).t ∧
        ∀ W : MME.DWZSourceAligned.AddressZWord.{u} outer,
          ∃ raw : ∀ s : Fin 15,
              MME.DWZComponentRestriction.PowIndex
                (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
                  (MME.DWZSquare.shapeZ s))
                (MME.DWZTable2Counts.component s * m),
            (∀ p : MME.DWZComponentRestriction.GroupedPosition m,
              HEq (MME.DWZComponentRestriction.PowIndex.get
                  (MME.DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
                (W (e p))) ∧
            f 2 (MME.DWZSourceAligned.coarseAddressZBasis K outer W) =
              MME.TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                    (MME.DWZTable2Counts.component s * m)) 2
                (fun s ↦
                  MME.DWZComponentRestriction.componentPowerZBasis K s m) raw := by
  sorry
