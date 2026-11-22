-- Prove2me | Theorems.Thm_P2M_Basis_smul_ntwist__ee7cf44200ea
-- name    : P2M_Basis_smul_ntwist__ee7cf44200ea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:47.804019+00:00
-- url     : https://prove2.me/theorems/08a6cdce-e925-4f4c-ac75-52c8992ac5a2
-- title:
--   P2 M Basis smul ntwist  ee7cf44200ea: P2 M Basis smul ntwist  ee7cf44200ea
-- statement:
--   The P2 M Basis smul ntwist  ee7cf44200ea construction uses the P2 M Basis smul ntwist  ee7cf44200ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L507-L515
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L507-L515

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

theorem P2M_Basis_smul_ntwist__ee7cf44200ea (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℕ) :
    ϖ • (b.ntwist₂ hϖ n m).toSubmodule (R := R) = (b.ntwist₂ hϖ (n + 1) (m + 1)).toSubmodule := by sorry

alias «Basis».«smul_ntwist₂» := P2M_Basis_smul_ntwist__ee7cf44200ea
