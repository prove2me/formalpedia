-- Prove2me | Theorems.Thm_P2M_Basis_ntwist__toSubmodule_le_6698b043c57e
-- name    : P2M_Basis_ntwist__toSubmodule_le_6698b043c57e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:13:04.168783+00:00
-- url     : https://prove2.me/theorems/84a0123e-78f5-4b7f-8a99-348e9e6df1d0
-- title:
--   P2 M Basis ntwist  to Submodule le 6698b043c57e: P2 M Basis ntwist  to Submodule le 6698b043c57e
-- statement:
--   The P2 M Basis ntwist  to Submodule le 6698b043c57e construction uses the P2 M Basis ntwist  to Submodule le 6698b043c57e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L566-L571
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L566-L571

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

theorem P2M_Basis_ntwist__toSubmodule_le_6698b043c57e (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℕ) :
    (b.ntwist₂ hϖ n m).toSubmodule ≤ b.toSubmodule (R := R) := by sorry

alias «Basis».«ntwist₂_toSubmodule_le» := P2M_Basis_ntwist__toSubmodule_le_6698b043c57e
