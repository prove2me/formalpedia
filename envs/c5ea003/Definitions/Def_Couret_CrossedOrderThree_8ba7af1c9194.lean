-- Prove2me | Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
-- name    : Couret_CrossedOrderThree_8ba7af1c9194
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:20.567059+00:00
-- url     : https://prove2.me/theorems/40ffba68-3ff2-4a26-8989-c77f9d66a6bf
-- title:
--   Threefold displacement for crossed matching
-- statement:
--   In Couret.Strobo2Tors, tripleDelta(a,b) is (b-a)+(b-a)+(b-a) in an additive abelian group G. This bundle retains only that displacement definition. It imposes no equation saying the displacement vanishes and contains no matching equivalence or equal-square classification.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/CrossedOrderThree.lean; source file SHA-256 c260e4e04ee42a43b8f1bfe9207a0e563323959fc9904fcf6de4efc377ad6dd0

import Mathlib
import Definitions.Def_Couret_RectangleFibres_2930a0e95467

/-!
STROBO-2TORS: normalized type-II crossed matching.

This theorem isolates the 3-torsion obstruction in the branch where the
singleton representatives have been aligned (d = b).
It proves equivalence at the level of equal two-point cosets, not yet
equivalence with SameSquare of arbitrary triple supports.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Three times the displacement from the double fibre to the singleton. -/
def tripleDelta (a b : G) : G :=
  (b - a) + (b - a) + (b - a)





end Couret.Strobo2Tors


