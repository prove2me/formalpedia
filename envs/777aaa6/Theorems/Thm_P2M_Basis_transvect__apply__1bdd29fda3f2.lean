-- Prove2me | Theorems.Thm_P2M_Basis_transvect__apply__1bdd29fda3f2
-- name    : P2M_Basis_transvect__apply__1bdd29fda3f2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:05.947755+00:00
-- url     : https://prove2.me/theorems/84754e7b-02b3-4207-b363-e7e2f0f14c03
-- title:
--   P2 M Basis transvect  apply  1bdd29fda3f2: P2 M Basis transvect  apply  1bdd29fda3f2
-- statement:
--   The P2 M Basis transvect  apply  1bdd29fda3f2 construction uses the P2 M Basis transvect  apply  1bdd29fda3f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L81-L83
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L81-L83

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem P2M_Basis_transvect__apply__1bdd29fda3f2 (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvect' x 0 = b 0 := by sorry

alias «Basis».«transvect'_apply₀» := P2M_Basis_transvect__apply__1bdd29fda3f2
