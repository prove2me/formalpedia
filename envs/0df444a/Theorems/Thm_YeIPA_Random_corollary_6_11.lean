-- Prove2me | Theorems.Thm_YeIPA_Random_corollary_6_11
-- name    : YeIPA.Random.corollary_6_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:09.233423+00:00
-- url     : https://prove2.me/theorems/0ca4b0d9-a1df-4b7d-8a65-5e3f03e26b6b
-- title:
--   Corollary 6.11 — a standard Gaussian system (6.5) is feasible with probability $p_{nd}$ (Wendel's formula)
-- statement:
--   Let $1\le n$ and $0\le m\le n$, put $d=n-m$, and let $A\in\mathbb R^{m\times n}$ be standard Gaussian: its $mn$ entries are independent $N(0,1)$ random variables. Then the probability that the homogeneous system (6.5)
--   $$Ax=0,\qquad x\ge0,\qquad x\ne0$$
--   has a feasible point is
--   $$p_{nd}=\frac{\binom{n-1}{0}+\cdots+\binom{n-1}{d-1}}{2^{n-1}}.$$
--
--   Equivalently, $1-p_{nm}$ is the probability that the $n$ random columns of $A$ lie in an open half-space through the origin of $\mathbb R^m$, which is Wendel's formula (1962). It is the base of the chapter's random-problem analysis: it says how likely a random homogeneous system is to be feasible.
--
--   **Formalization Note** The probability is the measure, under the product of standard Gaussians on the $mn$ entries, of the set of matrices for which (6.5) has a solution, compared with $p_{nd}$ as an extended nonnegative real. The section's standing assumption that $A$ has full row rank (p. 187) is carried as $m\le n$, under which a Gaussian $A$ has rank $m$ with probability one; $n\ge1$ makes $2^{n-1}$ and $\binom{n-1}{i}$ meaningful. For $m=n$ the formula gives $p_{n0}=0$, and for $m=0$ it gives $p_{nn}=1$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 193, Corollary 6.11

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory ProbabilityTheory

namespace YeIPA.Random

/-- Corollary 6.11 (Ye 1997, p. 193). Let every entry of `A ∈ ℝ^{m×n}` be an independent
standard Gaussian variable and `d = n − m`. The probability that system (6.5)
`Ax = 0, x ≥ 0, x ≠ 0` has a feasible point is
`p_nd = (C(n−1, 0) + ⋯ + C(n−1, d−1)) / 2^{n−1}`.
Standing hypotheses of §6.2 made explicit: `n ≥ 1`, and `m ≤ n` (so that `A` has full row rank
`m` with probability one, p. 187). -/
theorem corollary_6_11 {m n : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) :
    gaussianMatrix m n {A | ∃ x, IsFeasible65 (Matrix.of A) x} =
      ENNReal.ofReal (pnd n (n - m)) := by sorry

end YeIPA.Random
