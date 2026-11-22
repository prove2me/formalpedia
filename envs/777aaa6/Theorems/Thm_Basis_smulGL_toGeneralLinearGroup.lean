-- Prove2me | Theorems.Thm_Basis_smulGL_toGeneralLinearGroup
-- name    : Basis.smulGL_toGeneralLinearGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:18:30.705101+00:00
-- url     : https://prove2.me/theorems/9c13ae13-0b1e-4f4c-be30-789503481a64
-- title:
--   Basis: smul GL to General Linear Group
-- statement:
--   The Basis construction uses the smul GL to General Linear Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L452-L455
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L452-L455

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

theorem Basis.smulGL_toGeneralLinearGroup (g : GL ι K) (b : Basis ι K (ι → K)) :
    (g • b).toGeneralLinearGroup = g * b.toGeneralLinearGroup := by sorry
