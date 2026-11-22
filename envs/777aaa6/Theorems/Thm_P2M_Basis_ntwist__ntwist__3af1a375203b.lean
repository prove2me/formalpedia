-- Prove2me | Theorems.Thm_P2M_Basis_ntwist__ntwist__3af1a375203b
-- name    : P2M_Basis_ntwist__ntwist__3af1a375203b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:26.938107+00:00
-- url     : https://prove2.me/theorems/8c86990c-480c-4c9b-ae3c-b4da46dea54c
-- title:
--   P2 M Basis ntwist  ntwist  3af1a375203b: P2 M Basis ntwist  ntwist  3af1a375203b
-- statement:
--   The P2 M Basis ntwist  ntwist  3af1a375203b construction uses the P2 M Basis ntwist  ntwist  3af1a375203b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L573-L579
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L573-L579

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

theorem P2M_Basis_ntwist__ntwist__3af1a375203b (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    (n₁ m₁ n₂ m₂ : ℕ) :
    (b.ntwist₂ hϖ n₁ m₁).ntwist₂ hϖ n₂ m₂ = b.ntwist₂ hϖ (n₁ + n₂) (m₁ + m₂) := by sorry

alias «Basis».«ntwist₂_ntwist₂» := P2M_Basis_ntwist__ntwist__3af1a375203b
