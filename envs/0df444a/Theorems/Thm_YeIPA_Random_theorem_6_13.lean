-- Prove2me | Theorems.Thm_YeIPA_Random_theorem_6_13
-- name    : YeIPA.Random.theorem_6_13
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:02.224602+00:00
-- url     : https://prove2.me/theorems/a2ef8cdb-b791-4da5-b8f6-9e3ae96222c4
-- title:
--   Theorem 6.13 — with probability one, exactly one of (6.5) and (6.11) is empty and the other has an interior feasible point
-- statement:
--   Let $1\le n$ and $0\le m\le n$, and let $A\in\mathbb R^{m\times n}$ be standard Gaussian: its $mn$ entries are independent $N(0,1)$ random variables. Consider the homogeneous system (6.5) and its alternative (6.11),
--   $$\text{(6.5)}\quad Ax=0,\ x\ge0,\ x\ne0;\qquad\qquad \text{(6.11)}\quad s=A^Ty\ge0,\ s\ne0.$$
--   With probability one, exactly one of the two systems is empty and the other has an interior feasible point: either (6.5) has no solution and some $y$ gives $A^Ty>0$, or (6.11) has no solution and some $x>0$ satisfies $Ax=0$.
--
--   For an arbitrary matrix both systems can be feasible at once, and a feasible system need not have an interior point. The theorem says that these degenerate configurations have probability zero for a Gaussian matrix, so a random homogeneous feasibility problem is strictly feasible on whichever side is feasible. This is the starting point of the chapter's average-case bound of $O(\sqrt n\log n)$ iterations for random feasibility and LP problems.
--
--   **Formalization Note** "With probability one" is stated as: the set of matrices for which the conclusion fails is a null set of the product of standard Gaussians on the $mn$ entries (an almost-everywhere statement for that specific measure). The conclusion is the disjunction of the two cases; each case already implies that exactly one system is empty. The standing full-row-rank assumption of §6.2 (p. 187) is carried as $m\le n$, under which a Gaussian $A$ has rank $m$ with probability one, and $n\ge1$ excludes the empty system, where both (6.5) and (6.11) are empty.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 194, Theorem 6.13

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory ProbabilityTheory

namespace YeIPA.Random

/-- Theorem 6.13 (Ye 1997, p. 194). Let every entry of `A ∈ ℝ^{m×n}` be an independent
standard Gaussian variable. With probability one, exactly one of systems (6.5)
`Ax = 0, x ≥ 0, x ≠ 0` and (6.11) `s = Aᵀy ≥ 0, s ≠ 0` is empty and the other has an interior
feasible point: the set of `A` for which this fails has probability zero.
Standing hypotheses of §6.2 made explicit: `n ≥ 1`, and `m ≤ n` (so that `A` has full row rank
`m` with probability one, p. 187). -/
theorem theorem_6_13 {m n : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) :
    ∀ᵐ A ∂gaussianMatrix m n,
      ((¬ ∃ x, IsFeasible65 (Matrix.of A) x) ∧ ∃ y, IsInterior611 (Matrix.of A) y) ∨
      ((¬ ∃ y, IsFeasible611 (Matrix.of A) y) ∧ ∃ x, IsInterior65 (Matrix.of A) x) := by sorry

end YeIPA.Random
