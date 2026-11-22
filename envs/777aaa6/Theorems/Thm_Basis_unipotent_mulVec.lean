-- Prove2me | Theorems.Thm_Basis_unipotent_mulVec
-- name    : Basis.unipotent_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:17.794755+00:00
-- url     : https://prove2.me/theorems/5f76d0e7-5efc-405c-8abf-74bd6e7eadcb
-- title:
--   Basis: unipotent mul Vec
-- statement:
--   The Basis construction uses the unipotent mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L126-L128
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L126-L128

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem Basis.unipotent_mulVec (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (y : Fin 2 → K) :
    (b.unipotent x).val.mulVec y = b.transvectEquiv x y := by sorry
