-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareDeltaGraph_adj_iff
-- name    : Couret.STROBO2TORS.zeroFreeSquareDeltaGraph_adj_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:12.29614+00:00
-- url     : https://prove2.me/theorems/6e05bb2a-a0b8-43f5-b093-540eada6658f
-- title:
--   Exact zero-free collision adjacency
-- statement:
--   Let G be a finite abelian group, n=|G|, h=|G[2]| and t=|G[3]|. Let C_k be the number of unordered distinct triple-support pairs with equal labelled ordered squares and symmetric-difference size k. Let O_k count those with T=S+u for some 2u=0, and N_k those for which T is not any translate of S. A superscript zero means both supports avoid 0. All counts, subtraction and division below are in Nat. For any finite S,T and natural k, zero-free square-distance adjacency is equivalent to $$|S|=|T|=3,\quad S\ne T,\quad Q_S=Q_T,\quad|S\triangle T|=k,\quad0\notin S,\quad0\notin T.$$ All seven conditions are retained.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeDeltaCount.lean#L106-L114, lines 106–114; source file SHA-256 302023407fa92aa36bd7bd7c4099764736ee28c1a899b531c3a1166252b8c4b2; theorem Couret.STROBO2TORS.zeroFreeSquareDeltaGraph_adj_iff

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
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
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

theorem zeroFreeSquareDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (zeroFreeGraph (squareDeltaGraph (G := G) k)).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (S ∆ T).card = k ∧ 0 ∉ S ∧ 0 ∉ T := by sorry
















































end Finite

end Couret.STROBO2TORS
