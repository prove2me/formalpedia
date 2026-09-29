-- Prove2me | Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
-- name    : mme_basisZAllowed_map_eq_zero_of_selected_singletons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:47:05.180416+00:00
-- url     : https://prove2.me/theorems/3d588e57-d9ff-46ae-8658-4ecd75def5b3
-- title:
--   Singleton Z-slice vanishing implies whole basis-mask vanishing
-- statement:
--   Let a tensor be mapped modewise into another tensor whose Z mode has a fixed basis, and retain an arbitrary finite predicate of Z-basis labels. If replacing the Z map by the singleton projection onto each retained basis label makes the mapped tensor zero, then applying the entire retained-label Z projector also makes the tensor zero. This is the finite linear expansion that reduces a whole broken-copy mask to one canonical Z-word at a time.

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_basisZAllowed_map_eq_zero_of_selected_singletons
    {K : Type u} [Field K]
    {S T : TensorObj K 3} {I : Type u}
    [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed]
    (pre : ∀ i : Fin 3, S.V i →ₗ[K] T.V i)
    (hzero : ∀ j : I, allowed j →
      let G := T.basisZAllowedGrading bZ allowed
      let base : ∀ i : Fin 3, S.V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ (G.blockProj i 0).comp (pre i)
      let singleton : T.V 2 →ₗ[K] T.V 2 :=
        MME.DWZComponentRestriction.basisLabelProjection bZ id {j}
      PiTensorProduct.map
        (Function.update base 2
          ((G.blockProj 2 0).comp singleton |>.comp (pre 2))) S.t = 0) :
    let G := T.basisZAllowedGrading bZ allowed
    PiTensorProduct.map
      (fun i ↦ (G.blockProj i 0).comp (pre i)) S.t = 0 := by
  sorry
