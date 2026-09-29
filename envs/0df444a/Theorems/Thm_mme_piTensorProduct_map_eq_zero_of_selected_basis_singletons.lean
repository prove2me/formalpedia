-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
-- name    : mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:51:40.660434+00:00
-- url     : https://prove2.me/theorems/89bdde31-def1-488c-8097-44c544fcab97
-- title:
--   Selected singleton basis slices control a tensor selector
-- statement:
--   Let the mode-2 map of a three-tensor factor through a finite basis space and a selector that kills all disallowed basis labels. If the mapped tensor vanishes after restricting mode 2 to each allowed singleton basis label, then the complete mapped tensor vanishes. The other mode maps and the selector codomain are arbitrary.

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
    {K : Type u} [Field K]
    {S U : TensorObj K 3} {Z I : Type u}
    [AddCommGroup Z] [Module K Z]
    [Fintype I] [DecidableEq I]
    (bZ : Basis I K Z) (allowed : I → Prop)
    [DecidablePred allowed]
    (preZ : S.V 2 →ₗ[K] Z) (selectZ : Z →ₗ[K] U.V 2)
    (maps : ∀ i : Fin 3, S.V i →ₗ[K] U.V i)
    (hmodeTwo : maps 2 = selectZ.comp preZ)
    (hdisallowed : ∀ j : I, ¬ allowed j → selectZ (bZ j) = 0)
    (hzero : ∀ j : I, allowed j →
      let singleton : Z →ₗ[K] Z :=
        MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
      PiTensorProduct.map
        (Function.update maps 2
          ((selectZ.comp singleton).comp preZ)) S.t = 0) :
    PiTensorProduct.map maps S.t = 0 := by
  sorry
