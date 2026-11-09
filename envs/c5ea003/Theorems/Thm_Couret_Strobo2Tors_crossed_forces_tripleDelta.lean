-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_crossed_forces_tripleDelta
-- name    : Couret.Strobo2Tors.crossed_forces_tripleDelta
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:45:25.492514+00:00
-- url     : https://prove2.me/theorems/790a3ad8-8d6e-457d-9bff-7e0dbebe1db6
-- title:
--   A normalized crossed pair matching forces a third-period displacement
-- statement:
--   Let $G$ be a finite abelian group, $a,b,c,u\in G$ and $2u=0$. If
--
--   $$\{2c,2c+u\}=\{a+b,a+b+u\},\qquad\{c+b,c+b+u\}=\{2a,2a+u\},$$
--
--   then $3(b-a)\in\{0,u\}$. The case $u=0$ is allowed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/CrossedOrderThree.lean#L20-L62, lines 20–62; source file SHA-256 c260e4e04ee42a43b8f1bfe9207a0e563323959fc9904fcf6de4efc377ad6dd0; theorem Couret.Strobo2Tors.crossed_forces_tripleDelta

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_pair_coset_eq_iff
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

theorem crossed_forces_tripleDelta (a b c u : G)
    (hu : u + u = 0)
    (hfirst : pairSet (c + c) u = pairSet (a + b) u)
    (hsecond : pairSet (c + b) u = pairSet (a + a) u) :
    tripleDelta a b = 0 ∨ tripleDelta a b = u := by sorry




end Couret.Strobo2Tors
