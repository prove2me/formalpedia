-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.toLin_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:47:50.61044+00:00
-- url     : https://prove2.me/submissions/d16ae499-2973-44cf-9aed-fe73f886afbf

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
attribute [local simp] LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024
attribute [local simp] LinearMap.toMatrix'_mulVec_bruhat2024

set_option autoImplicit false

namespace Matrix.GeneralLinearGroup
theorem _root_.solution {n : Type*} [DecidableEq n]
    [Fintype n] {R : Type*} [CommRing R] (g : LinearMap.GeneralLinearGroup R (n → R))
    (x : n → R) :
    (Matrix.GeneralLinearGroup.toLin.symm g).val.mulVec x = g.val x := by
  simp [Matrix.GeneralLinearGroup.toLin, LinearMap.toMatrixAlgEquiv']
  exact LinearMap.toMatrix'_mulVec_bruhat2024 _ _
end Matrix.GeneralLinearGroup
