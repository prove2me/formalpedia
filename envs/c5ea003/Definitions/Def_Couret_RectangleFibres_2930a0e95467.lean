-- Prove2me | Definitions.Def_Couret_RectangleFibres_2930a0e95467
-- name    : Couret_RectangleFibres_2930a0e95467
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:32.321729+00:00
-- url     : https://prove2.me/theorems/9acf4bfc-4789-42fe-b87a-5a876d773a39
-- title:
--   Doubling values and two-pair rectangles
-- statement:
--   In an additive commutative group with decidable equality, defines doubleValue(x)=x+x, pairSet(x,u)={x,x+u}, and rectangleSet(x,y,u)=pairSet(x,u)∪pairSet(y,u). Finite sets remove repetitions: the definitions do not require nonzero u, two-torsion u, distinct doubled values or an ambient finite group. Any four-point or intrinsic-fibre interpretation requires additional hypotheses in the relevant theorems.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/RectangleFibres.lean; source file SHA-256 b58bd5cc6a9c03963265e4cd70ec907a0c62b9c159fe478c6e46672a7d4e1d68

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

def doubleValue (x : G) : G := x + x

def pairSet (x u : G) : Finset G := {x, x + u}

def rectangleSet (x y u : G) : Finset G :=
  pairSet x u ∪ pairSet y u













end Couret.Strobo2Tors


