-- Prove2me | Theorems.Thm_mme_dwz_owner_projection_standard_useful_block_tensor
-- name    : mme_dwz_owner_projection_standard_useful_block_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:28:34.77152+00:00
-- url     : https://prove2.me/theorems/dca091b8-5584-4481-b5ce-cc3aaaa800f1
-- title:
--   Owner Z projection keeps exactly its Table-2 useful-block tensor
-- statement:
--   Fix the canonical Table-2 grouped standard data, a useful block b, and an owner assignment. The Z projection retaining all labels assigned to a fixed owner t acts on the exact b-block tensor by $$P_t(T_b)=\begin{cases}T_b,&t=\operatorname{owner}(b),\\0,&t\ne\operatorname{owner}(b).\end{cases}$$ Both X and Y maps are identities. This specializes the labelled-basis projection calculus to the literal grouped standard-Z basis and useful-block address used in the DWZ Hole Lemma.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 5 Hole Lemma repair and Definitions 5.4 and 6.3 (PDF pp.47 and 53 / printed pp.46 and 52).

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_basis_label_owner_map_singleton

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_owner_projection_standard_useful_block_tensor
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) {s : ℕ}
    (owner : DWZStandardBlock m → Fin s) (t : Fin s)
    (block : DWZStandardBlock m) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection D.basis D.label
            (Finset.univ.filter (fun b ↦ t = owner b))))
        (dwzLabelledUsefulBlockTensor K m D block) =
      if t = owner block then
        dwzLabelledUsefulBlockTensor K m D block
      else 0 := by
  sorry
