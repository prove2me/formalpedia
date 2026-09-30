-- Prove2me | Theorems.Thm_Hirsch_q28_polar_no_length_three_between_links
-- name    : Hirsch.q28_polar_no_length_three_between_links
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T14:42:30.300892+00:00
-- url     : https://prove2.me/theorems/b922acbd-281e-42e3-867f-0a1403360b5f
-- title:
--   No length-three path between apex links of the $Q_{28}$ polar
-- statement:
--   Neighbours of the two apices of the polar of $Q_{28}$ are at combinatorial distance at least four.
--
--   Let $P=\{x\in\mathbb R^5:\langle a_i,x\rangle\le 1\}$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$, with apices $u=e_5$ and $v=-e_5$. Then there do not exist vertices $x,y$ of $P$ adjacent to $u$ and $v$ respectively together with a padded vertex-edge walk of length $3$ from $x$ to $y$.
--
--   This is the polar form of Proposition 2.3 of Matschke--Santos--Weibel: a transversal pair of geodesic maps in $S^3$ with no directed $2$-cycle in its reduced incidence pattern has width greater than $3$. Combined with the two apex-adjacent steps, this forbids a walk of length $5$ between the apices, which is the content of Corollary 2.9.
--
--   **Formalization Note.** Uses `q28A`, `q28B`, `q28U`, `q28V` from `Definitions.Def_Hirsch_q28`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Proposition 2.3 and Lemma 1.2 (maps width plus two base steps); polar form of Corollary 2.9.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28

open scoped RealInnerProductSpace

namespace Hirsch

theorem q28_polar_no_length_three_between_links :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      ¬ (Adj (Hpoly q28A q28B) q28U x ∧
          Adj (Hpoly q28A q28B) y q28V ∧
          ∃ w : ℕ → EuclideanSpace ℝ (Fin 5),
            w 0 = x ∧ w 3 = y ∧
              ∀ j < 3, w j = w (j + 1) ∨
                Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by sorry

end Hirsch
