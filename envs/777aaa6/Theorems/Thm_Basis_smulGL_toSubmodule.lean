-- Prove2me | Theorems.Thm_Basis_smulGL_toSubmodule
-- name    : Basis.smulGL_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:14.153247+00:00
-- url     : https://prove2.me/theorems/6ec84ee9-9bcf-42a4-9b49-9b0fcf4647c4
-- title:
--   Basis: smul GL to Submodule
-- statement:
--   The Basis construction uses the smul GL to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L415-L438
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L415-L438

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
variable [DecidableEq ι] [Fintype ι]

theorem Basis.smulGL_toSubmodule (g : GL ι K) (b : Basis ι K (ι → K)) :
    (g • b).toSubmodule (R := R) = g • b.toSubmodule := by sorry
