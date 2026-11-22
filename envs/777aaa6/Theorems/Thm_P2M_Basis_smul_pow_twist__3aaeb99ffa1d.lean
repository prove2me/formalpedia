-- Prove2me | Theorems.Thm_P2M_Basis_smul_pow_twist__3aaeb99ffa1d
-- name    : P2M_Basis_smul_pow_twist__3aaeb99ffa1d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:21.032801+00:00
-- url     : https://prove2.me/theorems/7bbc32ae-bc98-499f-adff-ee85abe393b7
-- title:
--   P2 M Basis smul pow twist  3aaeb99ffa1d: P2 M Basis smul pow twist  3aaeb99ffa1d
-- statement:
--   The P2 M Basis smul pow twist  3aaeb99ffa1d construction uses the P2 M Basis smul pow twist  3aaeb99ffa1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L537-L546
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L537-L546

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

theorem P2M_Basis_smul_pow_twist__3aaeb99ffa1d (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m k : ℤ) :
    ϖ.val ^ k • (b.twist₂ hϖ n m).toSubmodule (R := R) =
      (b.twist₂ hϖ (n + k) (m + k)).toSubmodule := by sorry

alias «Basis».«smul_pow_twist₂» := P2M_Basis_smul_pow_twist__3aaeb99ffa1d
