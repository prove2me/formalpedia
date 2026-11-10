-- Prove2me | Theorems.Thm_Niemeier_classification
-- name    : Niemeier.classification
-- status  : Open
-- author  : @chlee
-- created : 2026-11-09T09:46:30.828841+00:00
-- url     : https://prove2.me/theorems/25ef3422-7caa-43b8-b0cc-5ace3ef0e4ba
-- title:
--   Classification of the $24$ Niemeier isometry classes
-- statement:
--   There exists a family $(C_i)_{0\le i<24}$ of positive definite even unimodular integral lattices of rank $24$ such that $C_i$ and $C_j$ are integrally isometric exactly when $i=j$, every lattice with these properties is integrally isometric to exactly one $C_i$, and $C_i$ has no vector of squared norm $2$ exactly when $i=0$. Isometries are full integral isometries, without an orientation restriction.
-- source:
--   J. H. Conway and N. J. A. Sloane, On the enumeration of lattices of determinant one, Journal of Number Theory 15 (1982), 83–94, §2, Table III, §4 Tables V–VI and Theorem 2 (pp.91–93). https://doi.org/10.1016/0022-314X(82)90084-1

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Niemeier_Lattices24

set_option autoImplicit false
open Niemeier

theorem Niemeier.classification : ClassificationStatement:= by sorry
