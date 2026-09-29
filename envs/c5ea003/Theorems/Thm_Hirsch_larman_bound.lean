-- Prove2me | Theorems.Thm_Hirsch_larman_bound
-- name    : Hirsch.larman_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:26:38.04556+00:00
-- url     : https://prove2.me/theorems/68453b6b-bcef-4672-b877-d04e56527e3f
-- title:
--   Larman's bound $n\,2^{d-3}$
-- statement:
--   (Larman 1970.) Every nonempty bounded H-polytope in $\mathbb{R}^d$ described by $n$ inequalities has combinatorial diameter at most $n \cdot 2^{d-3}$. The bound is linear in the number of inequalities for each fixed dimension — still the best known bound of that shape. The exponent $d - 3$ is truncated natural subtraction, so for $d \le 3$ the asserted bound is $n$, which holds; lower-dimensional polytopes are included.
-- source:
--   Larman, Paths on polytopes, Proc. London Math. Soc. s3-20 (1970) 161-178, https://doi.org/10.1112/plms/s3-20.2.249

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem larman_bound (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by sorry

end Hirsch
