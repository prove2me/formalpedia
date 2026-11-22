-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.apply_ne_zero_of_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:53:36.98981+00:00
-- url     : https://prove2.me/submissions/1d9c3349-16f0-4bf1-bbd3-8b565d6ceb04

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
namespace Matrix.GeneralLinearGroup
theorem _root_.solution [Nontrivial R] (g : GL n R) (h : g.val.IsDiag)
    (j : n) : g j j ≠ 0 := by
  intro hzero
  apply g.det_ne_zero
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  by_cases hij : i = j
  · subst hij
    exact hzero
  · exact h hij
end Matrix.GeneralLinearGroup
