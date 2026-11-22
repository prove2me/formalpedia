-- Prove2me | Theorems.Thm_Basis_smulGL_def
-- name    : Basis.smulGL_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:14:56.978257+00:00
-- url     : https://prove2.me/theorems/ec35be56-f4a5-4d1b-8c37-1b82c88f14ed
-- title:
--   Basis: smul GL def
-- statement:
--   The Basis construction uses the smul GL def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L405-L407
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L405-L407

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

theorem Basis.smulGL_def (g : GL ι K) (b : Basis ι K (ι → K)) :
    g • b = b.map (g.toLin.toLinearEquiv) := by sorry
