-- Prove2me | Theorems.Thm_Basis_transvectEquiv_symm_mem_of_mem
-- name    : Basis.transvectEquiv_symm_mem_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:24.521232+00:00
-- url     : https://prove2.me/theorems/7dd361fb-6b22-49f8-b6d1-4f25ec11a4cd
-- title:
--   Basis: transvect Equiv symm mem of mem
-- statement:
--   The Basis construction uses the transvect Equiv symm mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L238-L249
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L238-L249

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}
variable [IsDiscreteValuationRing R]

theorem Basis.transvectEquiv_symm_mem_of_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : Fin 2 → K) (hy : y ∈ b.toSubmodule (R := R)) :
    (b.transvectEquiv x).symm y ∈ b.toSubmodule (R := R) := by sorry
