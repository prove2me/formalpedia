-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_rectangle_matching
-- name    : Couret.Strobo2Tors.rectangle_matching
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:49.064893+00:00
-- url     : https://prove2.me/theorems/95d4e0e6-b0a3-4910-bc64-fd50abf10b21
-- title:
--   Equal rectangles match their doubling fibres
-- statement:
--   Let G be a finite abelian group and x,y,u,a,b,v in G satisfy 2u=2v=0, 2x≠2y and 2a≠2b. Put P(x,u)={x,x+u} and R(x,y,u)=P(x,u)∪P(y,u). If the two rectangles R(x,y,u) and R(a,b,v) are equal, then $$[P(x,u)=P(a,v),\ P(y,u)=P(b,v)]\text{ or }[P(x,u)=P(b,v),\ P(y,u)=P(a,v)].$$ Neither shift is required nonzero.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/RectangleMatching.lean#L15-L75, lines 15–75; source file SHA-256 9046a87f21f5540b482541a6018e31546f63602657c5edea54bbe0e5bd4e59cb; theorem Couret.Strobo2Tors.rectangle_matching

import Definitions.Def_Couret_RectangleFibres_2930a0e95467
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_rectangle_equal_double_values
import Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_first
import Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_second
import Definitions.Def_Couret_RectangleFibres_2930a0e95467

/-!
STROBO: structural alternative for equality of two four-point rectangles.

Assuming each rectangle occupies two distinct fibres of the doubling map,
the pairs must match in their given order, or match after a swap.
This is a local theorem, not yet the convolution-square classification.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem rectangle_matching (x y u a b v : G)
    (hu : u + u = 0) (hv : v + v = 0)
    (hxy : doubleValue x ≠ doubleValue y)
    (hab : doubleValue a ≠ doubleValue b)
    (heq : rectangleSet x y u = rectangleSet a b v) :
    (pairSet x u = pairSet a v ∧ pairSet y u = pairSet b v) ∨
    (pairSet x u = pairSet b v ∧ pairSet y u = pairSet a v) := by sorry


end Couret.Strobo2Tors
