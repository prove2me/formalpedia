-- Prove2me | Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
-- name    : P2M_Basis_swap__apply__280e1e1cec15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:57.505986+00:00
-- url     : https://prove2.me/theorems/f4c0642d-a660-4e4f-879b-35a20f4c65f5
-- title:
--   P2 M Basis swap  apply  280e1e1cec15: P2 M Basis swap  apply  280e1e1cec15
-- statement:
--   The P2 M Basis swap  apply  280e1e1cec15 construction uses the P2 M Basis swap  apply  280e1e1cec15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L624-L624
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L624-L624

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

theorem P2M_Basis_swap__apply__280e1e1cec15 : swap₂ 0 = 1 := by sorry

alias «Basis».«swap₂_apply₀» := P2M_Basis_swap__apply__280e1e1cec15

attribute [defeq] P2M_Basis_swap__apply__280e1e1cec15
