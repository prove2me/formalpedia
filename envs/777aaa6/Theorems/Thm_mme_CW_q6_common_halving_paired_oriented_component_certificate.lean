-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_paired_oriented_component_certificate
-- name    : mme_CW_q6_common_halving_paired_oriented_component_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:37:30.179245+00:00
-- url     : https://prove2.me/theorems/415016e7-b10f-429d-8419-4572fd436c20
-- title:
--   Every paired oriented common-halving component is a matrix tensor of fixed volume
-- statement:
--   Fix one retained entry of a primary coupled q=6 family and one common coordinate halving. The product of the twice-cyclic block selected on the first half and the once-cyclic block selected on the second half is isomorphic to a concrete, potentially entry-dependent matrix-multiplication tensor. Although its three side lengths may vary with the retained entry, their product is exactly 6^(4G+2L). This is the sound local component fact behind the heterogeneous paired construction; it makes no mixed-family or inducedness claim.
-- source:
--   Coppersmith--Winograd (1990), four supported coupled constituent blocks and common-volume calculation on pp. 270--272; Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3/Table 2, cyclic 121/211 pairing.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data

open MME

universe u

set_option autoImplicit false

theorem mme_CW_q6_common_halving_paired_oriented_component_certificate
    {K : Type u} [Field K]
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) :
    TensorObj.Isomorphic
        (MMObj K
          (MME.PairedOrientedPackaging.componentM family halving p)
          (MME.PairedOrientedPackaging.componentN family halving p)
          (MME.PairedOrientedPackaging.componentP family halving p))
        (MME.PairedOrientedPackaging.componentObj
          (K := K) family halving p) ∧
      MME.PairedOrientedPackaging.componentM family halving p *
          MME.PairedOrientedPackaging.componentN family halving p *
          MME.PairedOrientedPackaging.componentP family halving p =
        6 ^ (4 * G + 2 * L) := by
  sorry
