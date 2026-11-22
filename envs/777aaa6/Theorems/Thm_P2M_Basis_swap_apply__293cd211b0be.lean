-- Prove2me | Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
-- name    : P2M_Basis_swap_apply__293cd211b0be
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:06.72181+00:00
-- url     : https://prove2.me/theorems/3df8087c-32f1-433c-b676-0cc27f68bb80
-- title:
--   P2 M Basis swap apply  293cd211b0be: P2 M Basis swap apply  293cd211b0be
-- statement:
--   The P2 M Basis swap apply  293cd211b0be construction uses the P2 M Basis swap apply  293cd211b0be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L632-L633
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L632-L633

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

theorem P2M_Basis_swap_apply__293cd211b0be (b : Basis (Fin 2) K (Fin 2 → K)) : b.swap 0 = b 1 := by sorry

alias «Basis».«swap_apply₀» := P2M_Basis_swap_apply__293cd211b0be
