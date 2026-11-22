-- Prove2me | Theorems.Thm_Basis_smulGL_apply
-- name    : Basis.smulGL_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:10:47.416663+00:00
-- url     : https://prove2.me/theorems/46fb1ad3-a349-4155-a4d0-0e6eebc3573f
-- title:
--   Basis: smul GL apply
-- statement:
--   The Basis construction uses the smul GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L410-L413
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L410-L413

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

theorem Basis.smulGL_apply (g : GL ι K) (b : Basis ι K (ι → K)) (i : ι) :
    (g • b) i = g.val.mulVec (b i) := by sorry
