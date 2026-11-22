-- Prove2me | Theorems.Thm_P2M_Basis_ntwist__le_ntwist__iff_9a842b8436ac
-- name    : P2M_Basis_ntwist__le_ntwist__iff_9a842b8436ac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:27.587725+00:00
-- url     : https://prove2.me/theorems/6a241bc3-e610-4e11-8bb4-7ee4033517b7
-- title:
--   P2 M Basis ntwist  le ntwist  iff 9a842b8436ac: P2 M Basis ntwist  le ntwist  iff 9a842b8436ac
-- statement:
--   The P2 M Basis ntwist  le ntwist  iff 9a842b8436ac construction uses the P2 M Basis ntwist  le ntwist  iff 9a842b8436ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L291-L297
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L291-L297

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
open BigOperators

theorem P2M_Basis_ntwist__le_ntwist__iff_9a842b8436ac (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    (n₁ m₁ n₂ m₂ : ℕ) :
    (b.ntwist₂ hϖ n₁ m₁).toSubmodule (R := R) ≤ (b.ntwist₂ hϖ n₂ m₂).toSubmodule ↔
      n₂ ≤ n₁ ∧ m₂ ≤ m₁ := by sorry

alias «Basis».«ntwist₂_le_ntwist₂_iff» := P2M_Basis_ntwist__le_ntwist__iff_9a842b8436ac
