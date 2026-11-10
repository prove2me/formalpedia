-- Prove2me | Theorems.Thm_Niemeier_isometryClasses_equiv_fin24
-- name    : Niemeier.isometryClasses_equiv_fin24
-- status  : Open
-- author  : @chlee
-- created : 2026-11-09T09:46:46.699452+00:00
-- url     : https://prove2.me/theorems/11f1bfc2-dbd3-460c-93c2-832e3a016c62
-- title:
--   The Niemeier isometry-class set has $24$ elements
-- statement:
--   The quotient of positive definite even unimodular integral rank-$24$ Gram lattices by full integral isometry admits a bijection with $\{0,\ldots,23\}$. This is a finite enumeration statement, not merely an equality using a cardinality function that defaults on infinite types.
-- source:
--   J. H. Conway and N. J. A. Sloane, On the enumeration of lattices of determinant one, Journal of Number Theory 15 (1982), 83–94, §2, Table III, §4 Tables V–VI and Theorem 2 (pp.91–93). https://doi.org/10.1016/0022-314X(82)90084-1

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Niemeier_Lattices24

set_option autoImplicit false
open Niemeier

theorem Niemeier.isometryClasses_equiv_fin24 : Nonempty (IsometryClass ≃ Fin 24):= by sorry
