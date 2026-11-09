-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union
-- name    : Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:41.017662+00:00
-- url     : https://prove2.me/theorems/8952f1be-900d-44b9-825f-ddb5310c6a4e
-- title:
--   Zero-free pair counts vanish at the union threshold
-- statement:
--   Let G be a finite abelian group, n=|G|, h=|G[2]| and t=|G[3]|. Let C_k be the number of unordered distinct triple-support pairs with equal labelled ordered squares and symmetric-difference size k. Let O_k count those with T=S+u for some 2u=0, and N_k those for which T is not any translate of S. A superscript zero means both supports avoid 0. All counts, subtraction and division below are in Nat. For natural k with n≤3+k/2, $$C_k^0=0.$$ The boundary equality is included.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeDeltaCount.lean#L168-L174, lines 168–174; source file SHA-256 302023407fa92aa36bd7bd7c4099764736ee28c1a899b531c3a1166252b8c4b2; theorem Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union

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
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_eq_translate_iff
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
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

theorem zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union (k : ℕ)
    (hn : Fintype.card G ≤ 3 + k / 2) :
    zeroFreeSquareDeltaPairCount (G := G) k = 0 := by sorry




































end Finite

end Couret.STROBO2TORS
