-- Prove2me | Theorems.Thm_P2M_Basis_transvect__apply__03ca5877df1c
-- name    : P2M_Basis_transvect__apply__03ca5877df1c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:32.725695+00:00
-- url     : https://prove2.me/theorems/ce011b00-43b6-4cf9-a109-5fad857b85cc
-- title:
--   P2 M Basis transvect  apply  03ca5877df1c: P2 M Basis transvect  apply  03ca5877df1c
-- statement:
--   The P2 M Basis transvect  apply  03ca5877df1c construction uses the P2 M Basis transvect  apply  03ca5877df1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L86-L88
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L86-L88

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem P2M_Basis_transvect__apply__03ca5877df1c (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvect' x 1 = x • b 0 + b 1 := by sorry

alias «Basis».«transvect'_apply₁» := P2M_Basis_transvect__apply__03ca5877df1c
