-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_second
-- name    : Couret.Strobo2Tors.rectangle_filter_second
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:44:25.683037+00:00
-- url     : https://prove2.me/theorems/88d956ce-0a5a-48d5-85b6-509bf158908d
-- title:
--   The second doubled value recovers its rectangle pair
-- statement:
--   Let $G$ be a finite abelian group and $R(x,y,u)=\{x,x+u,y,y+u\}$, $P(x,u)=\{x,x+u\}$. If $2u=0$ and $2x\ne2y$, then
--
--   $$\{z\in R(x,y,u):2z=2y\}=P(y,u).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/RectangleFibres.lean#L53-L60, lines 53–60; source file SHA-256 b58bd5cc6a9c03963265e4cd70ec907a0c62b9c159fe478c6e46672a7d4e1d68; theorem Couret.Strobo2Tors.rectangle_filter_second

import Definitions.Def_Couret_RectangleFibres_2930a0e95467
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_first
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

theorem rectangle_filter_second (x y u : G)
    (hu : u + u = 0) (hxy : doubleValue x ≠ doubleValue y) :
    (rectangleSet x y u).filter (fun z => doubleValue z = doubleValue y) =
      pairSet y u := by sorry






end Couret.Strobo2Tors
