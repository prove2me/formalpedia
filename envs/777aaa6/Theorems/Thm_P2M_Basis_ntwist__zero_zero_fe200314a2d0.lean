-- Prove2me | Theorems.Thm_P2M_Basis_ntwist__zero_zero_fe200314a2d0
-- name    : P2M_Basis_ntwist__zero_zero_fe200314a2d0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:29.00999+00:00
-- url     : https://prove2.me/theorems/58f0870b-8b9c-46e7-ab27-3e4266a898e2
-- title:
--   P2 M Basis ntwist  zero zero fe200314a2d0: P2 M Basis ntwist  zero zero fe200314a2d0
-- statement:
--   The P2 M Basis ntwist  zero zero fe200314a2d0 construction uses the P2 M Basis ntwist  zero zero fe200314a2d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L553-L558
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L553-L558

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

theorem P2M_Basis_ntwist__zero_zero_fe200314a2d0 (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    b.ntwist₂ hϖ 0 0 = b := by sorry

alias «Basis».«ntwist₂_zero_zero» := P2M_Basis_ntwist__zero_zero_fe200314a2d0
