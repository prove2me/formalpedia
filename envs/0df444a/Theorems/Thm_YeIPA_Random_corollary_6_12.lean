-- Prove2me | Theorems.Thm_YeIPA_Random_corollary_6_12
-- name    : YeIPA.Random.corollary_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:02.080355+00:00
-- url     : https://prove2.me/theorems/18e5aec7-da3b-41ae-9f3d-841a7b030150
-- title:
--   Corollary 6.12 — a standard Gaussian system (6.5) has an interior feasible point with probability $p_{nd}$
-- statement:
--   Let $1\le n$ and $0\le m\le n$, put $d=n-m$, and let $A\in\mathbb R^{m\times n}$ be standard Gaussian: its $mn$ entries are independent $N(0,1)$ random variables. Then the probability that the homogeneous system (6.5) has an interior feasible point, that is, some $x\in\mathbb R^n$ with
--   $$Ax=0,\qquad x>0,$$
--   is
--   $$p_{nd}=\frac{\binom{n-1}{0}+\cdots+\binom{n-1}{d-1}}{2^{n-1}}.$$
--
--   Together with Corollary 6.11 this says that a random homogeneous system which is feasible is, with probability one, strictly feasible: the probability of a feasible system without a strictly positive solution is zero.
--
--   **Formalization Note** The probability is the measure, under the product of standard Gaussians on the $mn$ entries, of the set of matrices for which some $x$ with every coordinate positive satisfies $Ax=0$, compared with $p_{nd}$ as an extended nonnegative real. The standing full-row-rank assumption (p. 187) is carried as $m\le n$, under which a Gaussian $A$ has rank $m$ with probability one; $n\ge1$ makes $p_{nd}$ meaningful.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 193, Corollary 6.12

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory ProbabilityTheory

namespace YeIPA.Random

/-- Corollary 6.12 (Ye 1997, p. 193). Let every entry of `A ∈ ℝ^{m×n}` be an independent
standard Gaussian variable and `d = n − m`. The probability that system (6.5) has an interior
feasible point (`Ax = 0`, `x > 0`) is `p_nd = (C(n−1, 0) + ⋯ + C(n−1, d−1)) / 2^{n−1}`.
Standing hypotheses of §6.2 made explicit: `n ≥ 1`, and `m ≤ n` (so that `A` has full row rank
`m` with probability one, p. 187). -/
theorem corollary_6_12 {m n : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) :
    gaussianMatrix m n {A | ∃ x, IsInterior65 (Matrix.of A) x} =
      ENNReal.ofReal (pnd n (n - m)) := by sorry

end YeIPA.Random
