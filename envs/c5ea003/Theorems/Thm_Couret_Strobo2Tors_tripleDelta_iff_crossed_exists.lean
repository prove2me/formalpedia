-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_tripleDelta_iff_crossed_exists
-- name    : Couret.Strobo2Tors.tripleDelta_iff_crossed_exists
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:58.028516+00:00
-- url     : https://prove2.me/theorems/4e124af2-3fd8-4023-af09-9d2bcb657ad5
-- title:
--   The third-period condition exactly characterizes a normalized crossed matching
-- statement:
--   Let $G$ be a finite abelian group, $a,b,u\in G$ and $2u=0$. Then
--
--   $$[\exists c,\{2c,2c+u\}=\{a+b,a+b+u\}\land\{c+b,c+b+u\}=\{2a,2a+u\}]\iff3(b-a)\in\{0,u\}.$$
--
--   This is a coset-matching theorem, not an unrestricted square-collision classification.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/CrossedOrderThree.lean#L64-L98, lines 64–98; source file SHA-256 c260e4e04ee42a43b8f1bfe9207a0e563323959fc9904fcf6de4efc377ad6dd0; theorem Couret.Strobo2Tors.tripleDelta_iff_crossed_exists

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_crossed_forces_tripleDelta
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

theorem tripleDelta_iff_crossed_exists (a b u : G) (hu : u + u = 0) :
    (∃ c : G,
      pairSet (c + c) u = pairSet (a + b) u ∧
      pairSet (c + b) u = pairSet (a + a) u) ↔
    tripleDelta a b = 0 ∨ tripleDelta a b = u := by sorry


end Couret.Strobo2Tors
