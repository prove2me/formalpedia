-- Prove2me | Theorems.Thm_BruhatTits_Lattice_smul_isSimilar
-- name    : BruhatTits.Lattice.smul_isSimilar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:56:50.159805+00:00
-- url     : https://prove2.me/theorems/7e33a061-b29f-4133-aa05-2f19f69c50d5
-- title:
--   Lattice: smul is Similar
-- statement:
--   The Lattice construction uses the smul is Similar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L406-L408
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L406-L408

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

theorem BruhatTits.Lattice.smul_isSimilar (L : Lattice R) (a : Kˣ) : IsSimilar R (a • L) L := by sorry
