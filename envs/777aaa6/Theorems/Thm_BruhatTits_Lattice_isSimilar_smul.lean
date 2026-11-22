-- Prove2me | Theorems.Thm_BruhatTits_Lattice_isSimilar_smul
-- name    : BruhatTits.Lattice.isSimilar_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:56:59.102796+00:00
-- url     : https://prove2.me/theorems/0fee6388-92c0-47f9-8229-af6751b521a7
-- title:
--   Lattice: is Similar smul
-- statement:
--   The Lattice construction uses the is Similar smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L404-L404
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L404-L404

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

theorem BruhatTits.Lattice.isSimilar_smul (L : Lattice R) (a : Kˣ) : IsSimilar R L (a • L) := by sorry
