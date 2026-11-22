-- Prove2me | Theorems.Thm_Basis_swapMatrix_smul_toSubmodule
-- name    : Basis.swapMatrix_smul_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:21:43.729404+00:00
-- url     : https://prove2.me/theorems/3c3af833-79bb-40ff-b5ad-99561e1b7873
-- title:
--   Basis: swap Matrix smul to Submodule
-- statement:
--   The Basis construction uses the swap Matrix smul to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L658-L660
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L658-L660

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

theorem Basis.swapMatrix_smul_toSubmodule (b : Basis (Fin 2) K (Fin 2 → K)) :
    b.swapMatrix • b.toSubmodule = b.swap.toSubmodule (R := R) := by sorry
