-- Prove2me | Theorems.Thm_Hirsch_q28_polar_no_length_five_walk
-- name    : Hirsch.q28_polar_no_length_five_walk
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T13:48:16.413269+00:00
-- url     : https://prove2.me/theorems/7d4aff6c-23f3-404f-902b-d1560d0c3a8a
-- title:
--   The $Q_{28}$ polar has no length-five path between apices
-- statement:
--   There is no padded vertex-edge walk of length $5$ from $u=e_5$ to $v=-e_5$ in the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$.
--
--   Let $a_1,\ldots,a_{28}$ be the listed vertices of $Q_{28}$ and
--   $$
--   P=\{x\in\mathbb R^5:\langle a_i,x\rangle\le 1\}.
--   $$
--   Then no sequence $w_0,\ldots,w_5$ of points with $w_0=e_5$, $w_5=-e_5$, and each step either stationary or an edge of $P$, exists. Equivalently, the graph distance between the two spindle apices is at least $6$, which is the polar form of the statement that $Q_{28}$ has width at least six.
--
--   This is the combinatorial content of Corollary 2.9 of Matschke--Santos--Weibel, obtained from a reduced incidence pattern with no directed $2$-cycle (their Proposition 2.3 / Theorem 2.7).
--
--   **Formalization Note** Uses `q28A`, `q28B`, `q28U`, `q28V` from `Definitions.Def_Hirsch_q28`. Walks match the mission `Adj`/`DiamLE` padding convention.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9, Proposition 2.3 and Theorem 2.7 (reduced incidence pattern implies width at least 6).

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28

open scoped RealInnerProductSpace

namespace Hirsch

theorem q28_polar_no_length_five_walk :
    ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
      ¬ (w 0 = q28U ∧ w 5 = q28V ∧
          ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by sorry

end Hirsch
