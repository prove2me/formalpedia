-- Prove2me | Theorems.Thm_Hirsch_santos_counterexample
-- name    : Hirsch.santos_counterexample
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:28:41.419529+00:00
-- url     : https://prove2.me/theorems/d98c975f-3efb-4c49-93db-280b05b44b10
-- title:
--   Santos: the Hirsch conjecture is false
-- statement:
--   (Santos 2012.) There exists a nonempty bounded H-polytope violating the Hirsch bound: for some $d$, $n$, and inequalities $\langle a_i, x\rangle \le b_i$, the polytope has two vertices joined by no path of at most $n - d$ edges. Santos's original example has dimension $43$ with $86$ facets and diameter at least $44$; Matschke, Santos, and Weibel later found one of dimension $20$ with $40$ facets and diameter $21$. Boundedness is essential — the unbounded version was already refuted by Klee--Walkup in 1967 — and is part of the statement.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, Annals of Mathematics 176 (2012) 383-412, https://arxiv.org/abs/1006.2814; smaller example: Matschke--Santos--Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015), https://arxiv.org/abs/1202.4701

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem santos_counterexample :
    ∃ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty ∧ Bornology.IsBounded (Hpoly a b) ∧
      ¬ DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch
