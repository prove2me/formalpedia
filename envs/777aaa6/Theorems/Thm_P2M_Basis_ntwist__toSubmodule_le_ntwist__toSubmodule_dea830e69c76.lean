-- Prove2me | Theorems.Thm_P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
-- name    : P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:35.852144+00:00
-- url     : https://prove2.me/theorems/640f03c0-4381-4f74-95d4-b7bd46be5c91
-- title:
--   P2 M Basis ntwist  to Submodule le ntwist  to Submodule dea830e69c76: P2 M Basis ntwist  to Submodule le ntwist  to Submodule dea830e69c76
-- statement:
--   The P2 M Basis ntwist  to Submodule le ntwist  to Submodule dea830e69c76 construction uses the P2 M Basis ntwist  to Submodule le ntwist  to Submodule dea830e69c76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L560-L564
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L560-L564

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

theorem P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76 (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R}
    (hϖ : Irreducible ϖ) {n₁ m₁ n₂ m₂ : ℕ} (hn : n₂ ≤ n₁) (hm : m₂ ≤ m₁) :
    (b.ntwist₂ hϖ n₁ m₁).toSubmodule (R := R) ≤ (b.ntwist₂ hϖ n₂ m₂).toSubmodule (R := R) := by sorry

alias «Basis».«ntwist₂_toSubmodule_le_ntwist₂_toSubmodule» := P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
