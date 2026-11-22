-- Prove2me | Theorems.Thm_P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
-- name    : P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:24.331466+00:00
-- url     : https://prove2.me/theorems/e8e45edd-091c-4f3d-bc83-590ccb1fc53e
-- title:
--   P2 M Basis transvect Equiv apply  b7ef14f0fd7c: P2 M Basis transvect Equiv apply  b7ef14f0fd7c
-- statement:
--   The P2 M Basis transvect Equiv apply  b7ef14f0fd7c construction uses the P2 M Basis transvect Equiv apply  b7ef14f0fd7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L97-L99
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L97-L99

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectEquiv x (b 0) = b 0 := by sorry

alias «Basis».«transvectEquiv_apply₀» := P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
