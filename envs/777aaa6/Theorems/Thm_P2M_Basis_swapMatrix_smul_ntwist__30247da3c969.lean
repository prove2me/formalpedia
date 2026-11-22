-- Prove2me | Theorems.Thm_P2M_Basis_swapMatrix_smul_ntwist__30247da3c969
-- name    : P2M_Basis_swapMatrix_smul_ntwist__30247da3c969
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:28.719638+00:00
-- url     : https://prove2.me/theorems/1d1fde60-fddb-4918-9183-796bf5a89ccf
-- title:
--   P2 M Basis swap Matrix smul ntwist  30247da3c969: P2 M Basis swap Matrix smul ntwist  30247da3c969
-- statement:
--   The P2 M Basis swap Matrix smul ntwist  30247da3c969 construction uses the P2 M Basis swap Matrix smul ntwist  30247da3c969 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L662-L678
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L662-L678

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

theorem P2M_Basis_swapMatrix_smul_ntwist__30247da3c969 (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    (n m : ℕ) :
    b.swapMatrix • (b.ntwist₂ hϖ n m).toSubmodule = (b.ntwist₂ hϖ m n).toSubmodule (R := R) := by sorry

alias «Basis».«swapMatrix_smul_ntwist₂» := P2M_Basis_swapMatrix_smul_ntwist__30247da3c969
