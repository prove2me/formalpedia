-- Prove2me | Theorems.Thm_P2M_Basis_twist__le_twist__iff_0b153256402b
-- name    : P2M_Basis_twist__le_twist__iff_0b153256402b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:15:05.7741+00:00
-- url     : https://prove2.me/theorems/e41c41f1-2ae4-4c1d-bb2c-8d0fb279d1f8
-- title:
--   P2 M Basis twist  le twist  iff 0b153256402b: P2 M Basis twist  le twist  iff 0b153256402b
-- statement:
--   The P2 M Basis twist  le twist  iff 0b153256402b construction uses the P2 M Basis twist  le twist  iff 0b153256402b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L261-L276
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L261-L276

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

theorem P2M_Basis_twist__le_twist__iff_0b153256402b (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    (n₁ m₁ n₂ m₂ : ℤ) :
    (b.twist₂ hϖ n₁ m₁).toSubmodule (R := R) ≤ (b.twist₂ hϖ n₂ m₂).toSubmodule ↔
      n₂ ≤ n₁ ∧ m₂ ≤ m₁ := by sorry

alias «Basis».«twist₂_le_twist₂_iff» := P2M_Basis_twist__le_twist__iff_0b153256402b
