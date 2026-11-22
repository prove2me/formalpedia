-- Prove2me | Theorems.Thm_BruhatTits_Lattice_embDiagonal_smul_eq_smul
-- name    : BruhatTits.Lattice.embDiagonal_smul_eq_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:57:29.039783+00:00
-- url     : https://prove2.me/theorems/1ce4da29-137a-43ce-997a-9b81afc8d097
-- title:
--   Lattice: emb Diagonal smul eq smul
-- statement:
--   The Lattice construction uses the emb Diagonal smul eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L370-L375
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean#L370-L375

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
omit [IsFractionRing R K]

theorem BruhatTits.Lattice.embDiagonal_smul_eq_smul (L : Lattice R) (u : Kˣ) :
    Matrix.GeneralLinearGroup.embDiagonal _ (Fin 2) u • L = u • L := by sorry
