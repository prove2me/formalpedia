-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_rectangle_equal_double_values
-- name    : Couret.Strobo2Tors.rectangle_equal_double_values
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:53.014206+00:00
-- url     : https://prove2.me/theorems/ead8ce57-b070-457e-baaf-a56fe26e38bd
-- title:
--   Equal rectangles have equal doubled-value sets
-- statement:
--   Let $G$ be a finite abelian group and $R(x,y,u)=\{x,x+u,y,y+u\}$, $P(x,u)=\{x,x+u\}$. If $2u=2v=0$ and $R(x,y,u)=R(a,b,v)$, then
--
--   $$\{2x,2y\}=\{2a,2b\}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/RectangleFibres.lean#L73-L84, lines 73–84; source file SHA-256 b58bd5cc6a9c03963265e4cd70ec907a0c62b9c159fe478c6e46672a7d4e1d68; theorem Couret.Strobo2Tors.rectangle_equal_double_values

import Definitions.Def_Couret_RectangleFibres_2930a0e95467
import Mathlib
import Definitions.Def_Couret_Prelude_5b3cc8c481fb

/-!
STROBO type-II rectangle: intrinsic recovery of the two doubled fibres.
This file does not prove the full universal collision classification.

Given u+u=0 and doubleValue x != doubleValue y, the four-point
rectangle {x,x+u,y,y+u} splits canonically by the doubling map into
the two sets {x,x+u} and {y,y+u}.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem rectangle_equal_double_values (x y u a b v : G)
    (hu : u + u = 0) (hv : v + v = 0)
    (heq : rectangleSet x y u = rectangleSet a b v) :
    ({doubleValue x, doubleValue y} : Finset G) =
      ({doubleValue a, doubleValue b} : Finset G) := by sorry


end Couret.Strobo2Tors
