-- Prove2me | solution 1 for BruhatTits.Lattice.isSimilar_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:57:07.878875+00:00
-- url     : https://prove2.me/submissions/64800d8b-bfee-4382-990d-f48159c751ea

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
open BruhatTits
variable (R)
open BruhatTits.Lattice
attribute [instance] isLattice
variable {R}
variable [IsPrincipalIdealRing R]
variable (R)
omit [IsFractionRing R K] [IsPrincipalIdealRing R]
namespace BruhatTits.Lattice
theorem _root_.solution (L : Lattice R) (a : Kˣ) : IsSimilar R L (a • L) := ⟨a, rfl⟩
end BruhatTits.Lattice
