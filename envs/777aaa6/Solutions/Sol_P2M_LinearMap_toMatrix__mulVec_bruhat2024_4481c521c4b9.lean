-- Prove2me | solution 1 for P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:46:32.512434+00:00
-- url     : https://prove2.me/submissions/644ff840-ad89-4c00-a38f-f491f4985e2c

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
attribute [local simp] LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024

set_option autoImplicit false

namespace LinearMap
theorem _root_.solution {R : Type*} [CommSemiring R]
    {n : Type*} [DecidableEq n] [Fintype n] (f : (n → R) →ₗ[R] (n → R)) (x : n → R) :
    f.toMatrix'.mulVec x = f x := by
  classical
  have hy : x ∈ Submodule.span R (Set.range <| Pi.basisFun R n) := by
    rw [Module.Basis.span_eq]
    trivial
  induction' hy using Submodule.span_induction with y hy x y _ _ hx hy a x _ hx
  · obtain ⟨i, rfl⟩ := hy
    simp only [Pi.basisFun_apply, Matrix.mulVec_single, LinearMap.toMatrix'_apply, mul_one]
    ext j
    have : (fun j' ↦ if j' = i then (1 : R) else 0) = Pi.single i 1 := by aesop
    simp [this]
  · simp
  · simp [hx, hy, Matrix.mulVec_add]
  · simp [hx, Matrix.mulVec_smul]
end LinearMap
