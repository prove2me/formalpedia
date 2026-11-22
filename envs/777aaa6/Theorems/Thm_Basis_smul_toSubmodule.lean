-- Prove2me | Theorems.Thm_Basis_smul_toSubmodule
-- name    : Basis.smul_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:18:51.63244+00:00
-- url     : https://prove2.me/theorems/93b111e0-92ca-41b8-979c-4e0c8de36437
-- title:
--   Basis: smul to Submodule
-- statement:
--   The Basis construction uses the smul to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L477-L489
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L477-L489

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Matrix_GeneralLinearGroup_smul_toSubmodule

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι]
open Pointwise

theorem Basis.smul_toSubmodule (a : Kˣ) (b : Basis ι K (ι → K)) :
    a • b.toSubmodule (R := R) = (a • b).toSubmodule := by sorry
