-- Prove2me | Theorems.Thm_P2M_Basis_twist__eq_twist__iff_57624364f8f1
-- name    : P2M_Basis_twist__eq_twist__iff_57624364f8f1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:21:55.469427+00:00
-- url     : https://prove2.me/theorems/583227d4-c9fa-4521-ab45-9e66bf227ad4
-- title:
--   P2 M Basis twist  eq twist  iff 57624364f8f1: P2 M Basis twist  eq twist  iff 57624364f8f1
-- statement:
--   The P2 M Basis twist  eq twist  iff 57624364f8f1 construction uses the P2 M Basis twist  eq twist  iff 57624364f8f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L278-L289
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L278-L289

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

theorem P2M_Basis_twist__eq_twist__iff_57624364f8f1 (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    (n₁ m₁ n₂ m₂ : ℤ) :
    (b.twist₂ hϖ n₁ m₁).toSubmodule (R := R) = (b.twist₂ hϖ n₂ m₂).toSubmodule ↔
      n₂ = n₁ ∧ m₂ = m₁ := by sorry

alias «Basis».«twist₂_eq_twist₂_iff» := P2M_Basis_twist__eq_twist__iff_57624364f8f1
