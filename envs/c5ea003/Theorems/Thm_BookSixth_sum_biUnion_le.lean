-- Prove2me | Theorems.Thm_BookSixth_sum_biUnion_le
-- name    : BookSixth.sum_biUnion_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-16T15:04:56.126361+00:00
-- url     : https://prove2.me/theorems/a52980c2-28db-48af-b831-631671c0e235
-- title:
--   Weighted union bound over a finite union
-- statement:
--   Finite weighted union bound. Let $s$ be a finite index set, $t(i)$ finite sets, and $w$ a nonnegative real weight. The weight of the union is at most the sum of the weights. The proof is induction on the index set, splitting off one piece as a disjoint union up to an already-counted remainder. This is the subadditivity step behind every probabilistic-method existence argument formalized with explicit finite sums. **Formalization Note** Lean states nonnegativity globally and both sums with explicit `Finset.sum`.
-- source:
--   Standard finite union bound for weighted sums, as used in probabilistic-method existence arguments; cf. Alon--Spencer, The Probabilistic Method, Chapter 1 (union bound)

import Mathlib
import Definitions.Def_BookSixth

set_option autoImplicit false

theorem BookSixth.sum_biUnion_le (I A : Type) [DecidableEq I] [DecidableEq A]
    (s : Finset I) (t : I -> Finset A) (w : A -> Real)
    (hw : forall a, LE.le 0 (w a)) :
    LE.le (Finset.sum (s.biUnion t) w) (Finset.sum s (fun i => Finset.sum (t i) w)) := by sorry
