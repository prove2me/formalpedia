-- Prove2me | Theorems.Thm_Couret_Strobo2Tors_orderedRep_three
-- name    : Couret.Strobo2Tors.orderedRep_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:40.707936+00:00
-- url     : https://prove2.me/theorems/36d0ffaf-fcc3-43f9-9cfd-9e8dbfc657cc
-- title:
--   Ordered sum count of a three-element support
-- statement:
--   Let G be a finite additive commutative group with decidable equality. For any a,c,b,w in G with a≠c, a≠b and c≠b, the number orderedRep({a,c,b},w) of ordered pairs (x,y) in {a,c,b}×{a,c,b} satisfying x+y=w equals 1[a+a=w]+1[c+c=w]+1[b+b=w]+2·1[a+c=w]+2·1[a+b=w]+2·1[c+b=w], as an equality of natural numbers. Here each indicator is 1 if its equality holds and 0 otherwise. Different displayed sums may coincide, in which case their contributions add; no distinctness among these sums or restriction on w is assumed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/a91e50bc44e6bea233226b8e1090ba3e1b805b46/research/STROBO_2TORS_01/lean/STROBO2Tors/SquareExpansion.lean#L13-L29, lines 13–29; source file SHA-256 01be501848647215ec5106190839256dcf4cd37b939447c09e682624689abc6c; import module renamed from STROBO2Tors.SquareExpansion to Strobo2TorsSquareExpansion to disambiguate source modules; proof-only compatibility repair; declaration headers and elaborated theorem types preserved; theorem Couret.Strobo2Tors.orderedRep_three

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194

/-!
Exact expansion of a labelled triple convolution square.
This connects SameSquare to all nine ordered sums, including diagonals.
No assertion of complete classification or uniqueness is made here.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem orderedRep_three (a c b w : G)
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) :
    orderedRep ({a, c, b} : Finset G) w =
      (if a + a = w then 1 else 0) +
      (if c + c = w then 1 else 0) +
      (if b + b = w then 1 else 0) +
      2 * (if a + c = w then 1 else 0) +
      2 * (if a + b = w then 1 else 0) +
      2 * (if c + b = w then 1 else 0) := by sorry


end Couret.Strobo2Tors
