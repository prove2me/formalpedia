-- Prove2me | solution 1 for BruhatTits.Lattice.smul_isSimilar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:04.309178+00:00
-- url     : https://prove2.me/submissions/f44d93b4-9f4b-477c-92dd-eb220202effd

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
import Theorems.Thm_BruhatTits_Lattice_isSimilar_smul

set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
open BruhatTits
variable (R)
open BruhatTits.Lattice
attribute [instance] isLattice
variable {R}
variable [IsPrincipalIdealRing R]
variable (R)
omit [IsFractionRing R K] [IsPrincipalIdealRing R]
namespace BruhatTits.Lattice
theorem _root_.solution (L : Lattice R) (a : Kˣ) : IsSimilar R (a • L) L := by
  apply (IsSimilar.equivalence R).symm
  apply isSimilar_smul
end BruhatTits.Lattice
