-- Prove2me | solution 1 for IsLattice.of_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:32.07318+00:00
-- url     : https://prove2.me/submissions/a3ba7e7d-8b18-4f6e-bdee-34a3a68abb64

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
import Theorems.Thm_Submodule_span_eq_top_of_rank

set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]
omit [IsPrincipalIdealRing ↥R]
namespace IsLattice
theorem _root_.solution {M : Submodule R (ι → K)} (hfg : M.FG)
    (hr : Module.rank R M = Fintype.card ι) : IsLattice M where
  isFG := hfg
  spans := Submodule.span_eq_top_of_rank hr
end IsLattice
