-- Prove2me | Theorems.Thm_Hirsch_naddef_zero_one_bound
-- name    : Hirsch.naddef_zero_one_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:27:08.455026+00:00
-- url     : https://prove2.me/theorems/b39f16bd-cb64-4b54-8bc5-7a6e43fc5d26
-- title:
--   Naddef: $0/1$-polytopes have diameter at most $d$
-- statement:
--   (Naddef 1989.) If every vertex (extreme point) of a nonempty bounded H-polytope $P \subseteq \mathbb{R}^d$ has all coordinates in $\{0, 1\}$, then the combinatorial diameter of $P$ is at most $d$ — in particular such polytopes satisfy the Hirsch bound. The hypothesis is exactly that $P$ is a $0/1$-polytope: the convex hull of a set of $0/1$-vectors. The bound is the ambient dimension and is independent of the number of inequalities $n$.
-- source:
--   Naddef, The Hirsch conjecture is true for (0,1)-polytopes, Math. Programming 45 (1989) 109-110, https://doi.org/10.1007/BF01589418

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem naddef_zero_one_bound (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ i, x i = 0 ∨ x i = 1) :
    DiamLE (Hpoly a b) d := by sorry

end Hirsch
