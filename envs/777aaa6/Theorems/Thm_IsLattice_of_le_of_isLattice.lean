-- Prove2me | Theorems.Thm_IsLattice_of_le_of_isLattice
-- name    : IsLattice.of_le_of_isLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:56:55.342527+00:00
-- url     : https://prove2.me/theorems/4a89d9d2-201a-4f91-a5f6-ffc9d76e209c
-- title:
--   Is Lattice: of le of is Lattice
-- statement:
--   The Is Lattice construction uses the of le of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L61-L67
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L61-L67

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

theorem IsLattice.of_le_of_isLattice [IsNoetherianRing R]
    {M L P : Submodule R (ι → K)} [IsLattice M] [IsLattice P]
    (hML : M ≤ L) (hLP : L ≤ P) : IsLattice L := by sorry
