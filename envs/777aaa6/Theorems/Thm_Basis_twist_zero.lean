-- Prove2me | Theorems.Thm_Basis_twist_zero
-- name    : Basis.twist_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:14:36.135692+00:00
-- url     : https://prove2.me/theorems/7e22d1bf-f90f-4f82-9ab7-eb89c62d96fe
-- title:
--   Basis: twist zero
-- statement:
--   The Basis construction uses the twist zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L548-L551
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L548-L551

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
open Pointwise

theorem Basis.twist_zero (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    b.twist hϖ 0 = b := by sorry
