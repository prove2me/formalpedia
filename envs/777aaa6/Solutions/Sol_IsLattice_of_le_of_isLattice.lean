-- Prove2me | solution 1 for IsLattice.of_le_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:57:12.520217+00:00
-- url     : https://prove2.me/submissions/fe9f5dd2-c995-425a-bb91-d7d8046f41c8

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic

set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
open IsLattice
variable (M : Submodule R (ι → K)) [IsLattice M]
namespace IsLattice
theorem _root_.solution [IsNoetherianRing R]
    {M L P : Submodule R (ι → K)} [IsLattice M] [IsLattice P]
    (hML : M ≤ L) (hLP : L ≤ P) : IsLattice L where
  isFG := IsLattice.isFG.of_le hLP
  spans := by
    rw [eq_top_iff, ← IsLattice.spans (M := M)]
    exact Submodule.span_mono hML
end IsLattice
