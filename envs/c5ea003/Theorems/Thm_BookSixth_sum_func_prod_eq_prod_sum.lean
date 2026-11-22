-- Prove2me | Theorems.Thm_BookSixth_sum_func_prod_eq_prod_sum
-- name    : BookSixth.sum_func_prod_eq_prod_sum
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-16T16:43:32.950027+00:00
-- url     : https://prove2.me/theorems/883bbe50-ac31-4253-aee9-5ceb5247fdf9
-- title:
--   Function sums factor into product of sums
-- statement:
--   Sums over Boolean-valued functions factor as products of sums. For a finite type $A$ and $F : A \to \\{0,1\\} \to \mathbb{R}$, $$\sum_{b : A \to \\{0,1\\}} \prod_{e} F_e(b_e) = \prod_e (F_e(0) + F_e(1)).$$ The proof is induction on the index set, splitting functions by their value at the new point. This is the Fubini step behind every independent-coordinate expectation computation, including the $G(n,p)$ calculations. **Formalization Note** Lean states both sums over `Finset.univ` with explicit `Finset.sum` and `Finset.prod`.
-- source:
--   Fubini step for independent-coordinate expectations; cf. Alon--Spencer, The Probabilistic Method, Chapter 1

import Mathlib
import Definitions.Def_BookSixthRandomGraph

set_option autoImplicit false

theorem BookSixth.sum_func_prod_eq_prod_sum (A : Type) [DecidableEq A] [Fintype A]
    (F : A -> Bool -> Real) :
    Finset.sum Finset.univ (fun b : A -> Bool => Finset.prod Finset.univ (fun e => F e (b e)))
    = Finset.prod Finset.univ (fun e => (F e true + F e false)) := by sorry
