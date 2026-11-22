-- Prove2me | Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
-- name    : P2M_Basis_smul__apply_df6e729461ee
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:10:59.479157+00:00
-- url     : https://prove2.me/theorems/90b34a06-7e64-46a4-bc89-d0bbd496ed2b
-- title:
--   P2 M Basis smul  apply df6e729461ee: P2 M Basis smul  apply df6e729461ee
-- statement:
--   The P2 M Basis smul  apply df6e729461ee construction uses the P2 M Basis smul  apply df6e729461ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L472-L473
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L472-L473

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι]

theorem P2M_Basis_smul__apply_df6e729461ee (a : Kˣ) (b : Basis ι K (ι → K)) (i : ι) : (a • b) i = a • b i := by sorry

alias «Basis».«smul'_apply» := P2M_Basis_smul__apply_df6e729461ee
