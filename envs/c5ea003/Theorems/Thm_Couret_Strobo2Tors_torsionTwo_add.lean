-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_torsionTwo_add
-- name    : Couret.Strobo2Tors.torsionTwo_add
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:21.843601+00:00
-- url     : https://prove2.me/theorems/3f512be9-32e6-49ba-960b-b8b273d3c628
-- title:
--   The sum of two two-torsion elements is two-torsion
-- statement:
--   Let G be a finite abelian group and let $Q_S(w)$ count ordered pairs from the finite support S summing to w. If $a+a=b+b=0$, then $$(a+b)+(a+b)=0.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/Prelude.lean#L55-L59, lines 55–59; source file SHA-256 89fcdc8c9910bcaf6db0f9ef8c7ab2a0a0f7b5e04fda098817c5e55b8bab0dc9; theorem Couret.Strobo2Tors.torsionTwo_add

import Definitions.Def_Couret_Prelude_5b3cc8c481fb
import Mathlib
import Mathlib

/-!
STROBO-2TORS: exact finite-abelian triple-support model.

Scope of this module: definitions and elementary two-torsion lemmas ONLY.
The universal collision classification and count are NOT formalized here.
Until a pinned Lean build succeeds, this source is UNCOMPILED.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem torsionTwo_add (a b : G) (ha : a + a = 0) (hb : b + b = 0) :
    (a + b) + (a + b) = 0 := by sorry


end Couret.Strobo2Tors
