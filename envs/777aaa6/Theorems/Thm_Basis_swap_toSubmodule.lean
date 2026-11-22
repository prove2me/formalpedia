-- Prove2me | Theorems.Thm_Basis_swap_toSubmodule
-- name    : Basis.swap_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:19:24.880175+00:00
-- url     : https://prove2.me/theorems/8c29e593-ee0b-4c19-88e1-c6a664b15790
-- title:
--   Basis: swap to Submodule
-- statement:
--   The Basis construction uses the swap to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L638-L651
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L638-L651

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

theorem Basis.swap_toSubmodule (b : Basis (Fin 2) K (Fin 2 → K)) :
    b.swap.toSubmodule (R := R) = b.toSubmodule := by sorry
