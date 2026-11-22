-- Prove2me | Theorems.Thm_Basis_restrict_apply
-- name    : Basis.restrict_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:22.279039+00:00
-- url     : https://prove2.me/theorems/fe2527b9-e8ab-486b-b277-8f14580a1aa6
-- title:
--   Basis: restrict apply
-- statement:
--   The Basis construction uses the restrict apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L375-L377
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L375-L377

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
variable [IsFractionRing R K] [Fintype ι]

theorem Basis.restrict_apply (b : Basis ι K (ι → K)) (i : ι) :
    b.restrict (R := R) i = b i := by sorry
