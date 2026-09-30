-- Prove2me | Theorems.Thm_Hirsch_five_spindle_length_six
-- name    : Hirsch.five_spindle_length_six
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T13:24:47.06371+00:00
-- url     : https://prove2.me/theorems/8697af1d-650e-4a10-a2c5-de350daaffc8
-- title:
--   A five-dimensional spindle of length six
-- statement:
--   There exists a five-dimensional spindle of length six.
--
--   More precisely, there is an integer $n\ge 25$, a nonempty bounded H-polytope
--
--   $$
--   P=\{x\in\mathbb R^5:\langle a_i,x\rangle\le b_i,\ i=1,\ldots,n\}
--   $$
--
--   and a pair of extreme points $u,v$ of $P$ such that every describing inequality is tight at exactly one of $u$ or $v$, and there is no padded vertex-edge walk of length $5$ from $u$ to $v$. Equivalently, $P$ is a $5$-spindle of length at least six.
--
--   This is the polar of the $5$-prismatoid $Q_{28}$ of Matschke--Santos--Weibel (Corollary 2.9), or of their $25$-vertex prismatoid (Theorem 2.14): the two bases become the apices $u,v$, and the facet-ridge width of the prismatoid is the graph length of the spindle. Width at least six is obtained from a reduced incidence pattern with no $2$-cycle (Proposition 2.3).
--
--   **Formalization Note** The XOR condition is written as $\langle a_i,u\rangle=b_i$ if and only if $\langle a_i,v\rangle\neq b_i$. Walks are the mission's padded `Adj` walks of exact length $5$. Ambient dimension is five.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 (28-vertex prismatoid of width at least 6) and Theorem 2.14 (25-vertex prismatoid); polar form: F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Definition 1.4 and Theorem 1.6.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem five_spindle_length_six :
    ∃ (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 5)) (b : Fin n → ℝ)
      (u v : EuclideanSpace ℝ (Fin 5)),
      25 ≤ n ∧
      (Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hpoly a b) ∧
      u ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      (∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin 5),
        ¬ (w 0 = u ∧ w 5 = v ∧
            ∀ j < 5, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) := by sorry

end Hirsch
