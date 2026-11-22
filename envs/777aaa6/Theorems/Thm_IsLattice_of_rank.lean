-- Prove2me | Theorems.Thm_IsLattice_of_rank
-- name    : IsLattice.of_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:57:50.926342+00:00
-- url     : https://prove2.me/theorems/03ed1531-4fe6-4ed5-94ad-d2943cd8cb45
-- title:
--   Is Lattice: of rank
-- statement:
--   An `R`-submodule of `ι → K` that is finitely generated and has rank the cardinality of `ι` is
--   a lattice.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L294-L297
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L294-L297

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]
omit [IsPrincipalIdealRing ↥R]

theorem IsLattice.of_rank {M : Submodule R (ι → K)} (hfg : M.FG)
    (hr : Module.rank R M = Fintype.card ι) : IsLattice M := by sorry
