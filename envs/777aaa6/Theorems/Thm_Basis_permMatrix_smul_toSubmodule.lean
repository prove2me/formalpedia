-- Prove2me | Theorems.Thm_Basis_permMatrix_smul_toSubmodule
-- name    : Basis.permMatrix_smul_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:15.91227+00:00
-- url     : https://prove2.me/theorems/9478e281-4c48-40d8-85cf-385a53d7ed05
-- title:
--   Basis: perm Matrix smul to Submodule
-- statement:
--   The Basis construction uses the perm Matrix smul to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L607-L612
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L607-L612

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
variable [Fintype ι] [DecidableEq ι]

theorem Basis.permMatrix_smul_toSubmodule (b : Basis ι K (ι → K)) (e : ι ≃ ι) :
    b.permMatrix e • b.toSubmodule = Basis.toSubmodule (R := R) (b.reindex e) := by sorry
