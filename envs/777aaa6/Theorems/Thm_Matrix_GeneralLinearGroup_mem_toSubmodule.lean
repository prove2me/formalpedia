-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_mem_toSubmodule
-- name    : Matrix.GeneralLinearGroup.mem_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:44.813544+00:00
-- url     : https://prove2.me/theorems/63a2b493-de70-4114-9f2e-6cdd1e3bad52
-- title:
--   General Linear Group: mem to Submodule
-- statement:
--   The General Linear Group construction uses the mem to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L431-L480
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L431-L480

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
open Matrix.GeneralLinearGroup
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}

theorem Matrix.GeneralLinearGroup.mem_toSubmodule (g : GL ι K) (x : ι → K) :
    x ∈ g.toSubmodule (R := R) ↔ ∃ (y : ι → R), g *ᵥ (Subtype.val ∘ y) = x := by sorry
