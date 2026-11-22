-- Prove2me | Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
-- name    : P2M_Basis_swap__symm_e7ab2aa72738
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:31.393612+00:00
-- url     : https://prove2.me/theorems/b87622c7-8b4b-45db-be8c-4e5be712b5a2
-- title:
--   P2 M Basis swap  symm e7ab2aa72738: P2 M Basis swap  symm e7ab2aa72738
-- statement:
--   The P2 M Basis swap  symm e7ab2aa72738 construction uses the P2 M Basis swap  symm e7ab2aa72738 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L626-L626
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L626-L626

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

theorem P2M_Basis_swap__symm_e7ab2aa72738 : swap₂.symm = swap₂ := by sorry

alias «Basis».«swap₂_symm» := P2M_Basis_swap__symm_e7ab2aa72738

attribute [defeq] P2M_Basis_swap__symm_e7ab2aa72738
