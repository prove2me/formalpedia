-- Prove2me | Theorems.Thm_mme_complete_split_CW_square_cyclic_basis_transport
-- name    : mme_complete_split_CW_square_cyclic_basis_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:05:50.400965+00:00
-- url     : https://prove2.me/theorems/afacc7b5-aee2-4a3a-8669-067bf474cde4
-- title:
--   Cyclic canonical CW-square transport preserves every coarse basis pair and complete label
-- statement:
--   Let $K$ be a field, $q\ge0$ a natural CW parameter, and $\rho$ a coarse address of the canonical CW-square grading. Write $C_{q,\rho}$ for the literal corresponding block and $\pi$ for the cyclic permutation of its three modes. There are actual mode-wise linear equivalences
--
--   $$E_i:(\pi\cdot C_{q,\rho})_i\longrightarrow(C_{q,\rho\circ\pi^{-1}})_i$$
--
--   whose tensor product preserves the distinguished tensor. Each canonical subset-basis vector maps to the vector with the same ordered pair of CW coordinates in the target mode. Both fine grades, in their original factor order, are therefore preserved exactly. No source-isomorphism, basis-coherence, or profile-preservation assumption is supplied. This concrete source transport supports all-three-mode complete-profile restrictions from $112$ to $211$ and, by repeating the cycle, to $121$.
-- source:
--   Derived directly from the literal CWTensor, cwSquareCanonicalGrading, and coarseClassBasis definitions. Concrete q-parametric coordinate-map/projection construction adapted from the full accepted proof of mme_dwz_q6_canonical_121_swap_to_211_basis_transport (Prove2Me 7a6a318c-7171-4d84-8f2e-42fda32165cf), with cyclic rather than swap permutation, arbitrary q and rho, and basis action in all three modes. The concrete class maps simplify to identity linear equivalences after inspecting the three modes; their action on the actual canonical subset bases is definitional. Complete labels refer to More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions 3.4–3.6, pp. 14–15. This is an explicitly derived algebraic transport interface, not an additional numerical or hashing claim.

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_permutation

open MME MME.CompleteSplitCanonicalSquare

universe u

set_option autoImplicit false

theorem mme_complete_split_CW_square_cyclic_basis_transport
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj cyclicPerm (obj K q rho)).V i ≃ₗ[K]
          (obj K q (fun j ↦ rho (cyclicPerm.symm j))).V i,
      PiTensorProduct.map (fun i ↦ (maps i).toLinearMap)
          (TensorObj.permObj cyclicPerm (obj K q rho)).t =
        (obj K q (fun j ↦ rho (cyclicPerm.symm j))).t ∧
      (∀ (i : Fin 3) (p : Coord.{u} q rho (cyclicPerm.symm i)),
        maps i (basis K q rho (cyclicPerm.symm i) p) =
          basis K q (fun j ↦ rho (cyclicPerm.symm j)) i p) ∧
      (∀ (i : Fin 3) (p : Coord.{u} q rho (cyclicPerm.symm i)),
        label q (fun j ↦ rho (cyclicPerm.symm j)) i p =
          label q rho (cyclicPerm.symm i) p) := by sorry
