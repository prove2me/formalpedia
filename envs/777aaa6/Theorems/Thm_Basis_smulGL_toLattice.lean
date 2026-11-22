-- Prove2me | Theorems.Thm_Basis_smulGL_toLattice
-- name    : Basis.smulGL_toLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:20.595827+00:00
-- url     : https://prove2.me/theorems/d8c0a13a-a7c6-4682-97bb-ac41687eb7a5
-- title:
--   Basis: smul GL to Lattice
-- statement:
--   The Basis construction uses the smul GL to Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L440-L445
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L440-L445

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

theorem Basis.smulGL_toLattice (g : GL (Fin 2) K) (b : Basis (Fin 2) K (Fin 2 → K)) :
    (g • b).toLattice (R := R) = g • b.toLattice (R := R) := by sorry
