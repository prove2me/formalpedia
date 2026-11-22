-- Prove2me | solution 1 for Basis.transvectEquiv_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:53:35.815173+00:00
-- url     : https://prove2.me/submissions/f2f48fbe-fb55-4f2b-90a6-4a15d0eb205e

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
import Theorems.Thm_Basis_unipotent_mulVec
import Theorems.Thm_unipotent_pow_irred_smul_eq_submodule
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_smul
import Theorems.Thm_P2M_Basis_ntwist__zero_zero_fe200314a2d0


set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}
variable [IsDiscreteValuationRing R]
namespace Basis
theorem _root_.solution (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : Fin 2 → K) (hy : y ∈ b.toSubmodule (R := R)) :
    b.transvectEquiv x y ∈ b.toSubmodule (R := R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [← b.ntwist₂_zero_zero hϖ]
  rw [← unipotent_pow_irred_smul_eq_submodule (n := 0) (x := x), pow_zero, one_mul]
  rw [Matrix.GeneralLinearGroup.mem_smul]
  use y
  rw [b.ntwist₂_zero_zero]
  refine ⟨hy, ?_⟩
  rw [b.unipotent_mulVec]
  rfl
end Basis
