-- Prove2me | Theorems.Thm_P2M_Basis_transvect_apply__c6d95b5429da
-- name    : P2M_Basis_transvect_apply__c6d95b5429da
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:17.562173+00:00
-- url     : https://prove2.me/theorems/c30909e8-2ef9-4cdd-8c80-de802806f1ca
-- title:
--   P2 M Basis transvect apply  c6d95b5429da: P2 M Basis transvect apply  c6d95b5429da
-- statement:
--   The P2 M Basis transvect apply  c6d95b5429da construction uses the P2 M Basis transvect apply  c6d95b5429da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L65-L67
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L65-L67

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem P2M_Basis_transvect_apply__c6d95b5429da (b : Basis (Fin 2) K V) (x : K) :
    b.transvect x 0 = b 0 := by sorry

alias «Basis».«transvect_apply₀» := P2M_Basis_transvect_apply__c6d95b5429da
