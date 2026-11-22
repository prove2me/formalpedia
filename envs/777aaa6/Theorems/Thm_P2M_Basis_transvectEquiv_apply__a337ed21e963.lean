-- Prove2me | Theorems.Thm_P2M_Basis_transvectEquiv_apply__a337ed21e963
-- name    : P2M_Basis_transvectEquiv_apply__a337ed21e963
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:18.63017+00:00
-- url     : https://prove2.me/theorems/1e27eda6-b926-4a6f-a935-a9116599585c
-- title:
--   P2 M Basis transvect Equiv apply  a337ed21e963: P2 M Basis transvect Equiv apply  a337ed21e963
-- statement:
--   The P2 M Basis transvect Equiv apply  a337ed21e963 construction uses the P2 M Basis transvect Equiv apply  a337ed21e963 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L102-L104
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L102-L104

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem P2M_Basis_transvectEquiv_apply__a337ed21e963 (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectEquiv x (b 1) = x • b 0 + b 1 := by sorry

alias «Basis».«transvectEquiv_apply₁» := P2M_Basis_transvectEquiv_apply__a337ed21e963
