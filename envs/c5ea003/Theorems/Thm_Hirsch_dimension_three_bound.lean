-- Prove2me | Theorems.Thm_Hirsch_dimension_three_bound
-- name    : Hirsch.dimension_three_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:26:06.441689+00:00
-- url     : https://prove2.me/theorems/cf588038-4ee8-4c90-b034-348c28d0da21
-- title:
--   The Hirsch bound in dimension at most 3
-- statement:
--   (Klee 1966; Klee--Walkup 1967.) Every nonempty bounded H-polytope in $\mathbb{R}^d$ with $d \le 3$, described by $n$ inequalities, has combinatorial diameter at most $n - d$. Klee determined the exact maximum diameter $\lfloor 2n/3\rfloor - 1$ for $3$-polytopes with $n$ facets, which is below $n-3$; dimensions $0,1,2$ are elementary. Here $n$ counts the inequalities of the given description (at least the number of facets), the subtraction is truncated natural subtraction, and lower-dimensional polytopes in $\mathbb{R}^d$ are included — the stated bound holds for them as well.
-- source:
--   Klee, Diameters of polyhedral graphs, Canad. J. Math. 16 (1964) 602-614, and Klee--Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), https://doi.org/10.1007/BF02392971

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem dimension_three_bound (d n : ℕ) (hd : d ≤ 3)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch
