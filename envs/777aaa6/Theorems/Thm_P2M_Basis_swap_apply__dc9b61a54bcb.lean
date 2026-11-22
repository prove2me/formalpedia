-- Prove2me | Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
-- name    : P2M_Basis_swap_apply__dc9b61a54bcb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:38.58758+00:00
-- url     : https://prove2.me/theorems/de20f459-2f56-4e58-b617-6b764d9c40dc
-- title:
--   P2 M Basis swap apply  dc9b61a54bcb: P2 M Basis swap apply  dc9b61a54bcb
-- statement:
--   The P2 M Basis swap apply  dc9b61a54bcb construction uses the P2 M Basis swap apply  dc9b61a54bcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L635-L636
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L635-L636

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

theorem P2M_Basis_swap_apply__dc9b61a54bcb (b : Basis (Fin 2) K (Fin 2 → K)) : b.swap 1 = b 0 := by sorry

alias «Basis».«swap_apply₁» := P2M_Basis_swap_apply__dc9b61a54bcb
