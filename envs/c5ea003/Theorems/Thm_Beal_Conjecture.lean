-- Prove2me | Theorems.Thm_Beal_Conjecture
-- name    : Beal_Conjecture
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:45:23.675378+00:00
-- url     : https://prove2.me/theorems/c6651ce9-e1b6-432d-9816-71806e18b2dd
-- statement:
--   **Beal conjecture.** If $A,B,C,x,y,z$ are positive integers with $x,y,z>2$ and $A^x+B^y=C^z$, then $A,B,C$ have a common prime factor (i.e. $\gcd(A,B,C)>1$). (Statement following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/BealConjecture.lean

import Mathlib

theorem Beal_Conjecture : ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z → 1 < Finset.gcd ({A, B, C} : Finset ℕ) id := by sorry
