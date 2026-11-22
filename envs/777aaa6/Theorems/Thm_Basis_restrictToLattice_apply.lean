-- Prove2me | Theorems.Thm_Basis_restrictToLattice_apply
-- name    : Basis.restrictToLattice_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:10:40.933183+00:00
-- url     : https://prove2.me/theorems/c3a02dd8-5227-4883-9c23-4b2943adede1
-- title:
--   Basis: restrict To Lattice apply
-- statement:
--   The Basis construction uses the restrict To Lattice apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L386-L390
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L386-L390

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

theorem Basis.restrictToLattice_apply (b : Basis (Fin 2) K (Fin 2 → K)) (i : Fin 2) :
    @DFunLike.coe no_index _ _ _ _ (b.restrictToLattice (R := R)) i = b i := by sorry
