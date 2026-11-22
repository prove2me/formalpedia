-- Prove2me | Theorems.Thm_P2M_Basis_transvect_apply__3554c878d91a
-- name    : P2M_Basis_transvect_apply__3554c878d91a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:58.634761+00:00
-- url     : https://prove2.me/theorems/78102032-1dab-47fb-96db-bb5984d7338d
-- title:
--   P2 M Basis transvect apply  3554c878d91a: P2 M Basis transvect apply  3554c878d91a
-- statement:
--   The P2 M Basis transvect apply  3554c878d91a construction uses the P2 M Basis transvect apply  3554c878d91a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L69-L71
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L69-L71

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem P2M_Basis_transvect_apply__3554c878d91a (b : Basis (Fin 2) K V) (x : K) :
    b.transvect x 1 = x • b 0 + b 1 := by sorry

alias «Basis».«transvect_apply₁» := P2M_Basis_transvect_apply__3554c878d91a
