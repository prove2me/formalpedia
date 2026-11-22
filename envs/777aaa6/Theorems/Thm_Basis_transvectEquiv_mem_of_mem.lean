-- Prove2me | Theorems.Thm_Basis_transvectEquiv_mem_of_mem
-- name    : Basis.transvectEquiv_mem_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:30.843544+00:00
-- url     : https://prove2.me/theorems/ded73503-569d-4998-8d66-0260c45b13d1
-- title:
--   Basis: transvect Equiv mem of mem
-- statement:
--   The Basis construction uses the transvect Equiv mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L225-L236
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L225-L236

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}
variable [IsDiscreteValuationRing R]

theorem Basis.transvectEquiv_mem_of_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : Fin 2 → K) (hy : y ∈ b.toSubmodule (R := R)) :
    b.transvectEquiv x y ∈ b.toSubmodule (R := R) := by sorry
