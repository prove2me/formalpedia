-- Prove2me | Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
-- name    : P2M_Basis_swap__apply__cd04b6b0ed1e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:02.520938+00:00
-- url     : https://prove2.me/theorems/57c81b4c-7111-4f28-84fa-c1ee279b2359
-- title:
--   P2 M Basis swap  apply  cd04b6b0ed1e: P2 M Basis swap  apply  cd04b6b0ed1e
-- statement:
--   The P2 M Basis swap  apply  cd04b6b0ed1e construction uses the P2 M Basis swap  apply  cd04b6b0ed1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L625-L625
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L625-L625

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

theorem P2M_Basis_swap__apply__cd04b6b0ed1e : swap₂ 1 = 0 := by sorry

alias «Basis».«swap₂_apply₁» := P2M_Basis_swap__apply__cd04b6b0ed1e

attribute [defeq] P2M_Basis_swap__apply__cd04b6b0ed1e
