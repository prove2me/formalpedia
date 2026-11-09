-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareDeltaPairCount_divisibility
-- name    : Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_divisibility
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:13.173782+00:00
-- url     : https://prove2.me/theorems/6cd8ee77-a9f4-405a-b4ee-3945fc4f2caf
-- title:
--   Every zero-free count numerator is exactly divisible
-- statement:
--   Let G be a finite abelian group, n=|G|, h=|G[2]| and t=|G[3]|. Let C_k be the number of unordered distinct triple-support pairs with equal labelled ordered squares and symmetric-difference size k. Let O_k count those with T=S+u for some 2u=0, and N_k those for which T is not any translate of S. A superscript zero means both supports avoid 0. All counts, subtraction and division below are in Nat. The following four divisibilities hold simultaneously: $$4\mid(n-4)(n-2)(h-1),\quad2\mid(n-5)(h-1)(t-1),$$ $$12\mid(n-6)(n-2)(n-4)(h-1),\quad2\mid(n-6)(h-1)^2(t-1).$$ Natural truncated subtraction includes all small-group cases.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeDeltaCount.lean#L340-L352, lines 340–352; source file SHA-256 302023407fa92aa36bd7bd7c4099764736ee28c1a899b531c3a1166252b8c4b2; theorem Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_divisibility

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_six_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_eq_translate_iff
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_six_twelve_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_two_four_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_symmDiff_card
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_mul_edges
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered collision counts by symmetric difference after excluding zero
from both three-element supports. The proof transfers each translation-stable
branch by incidence counting. All subtractions and divisions are in Nat.
Historical unrestricted counts remain unchanged.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite

variable [Fintype G]

theorem zeroFreeSquareDeltaPairCount_divisibility :
    let n := Fintype.card G
    let h := (twoTorsion : Finset G).card
    let t := (threeTorsion : Finset G).card
    4 ∣ (n - 4) * (n - 2) * (h - 1) ∧
    2 ∣ (n - 5) * (h - 1) * (t - 1) ∧
    12 ∣ (n - 6) * (n - 2) * (n - 4) * (h - 1) ∧
    2 ∣ (n - 6) * (h - 1) ^ 2 * (t - 1) := by sorry


end Finite

end Couret.STROBO2TORS
