-- Prove2me | Theorems.Thm_RHLinalg_sum_sq_lower_of_card_pos_le
-- name    : RHLinalg.sum_sq_lower_of_card_pos_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:48.269254+00:00
-- url     : https://prove2.me/theorems/d4997750-a20a-4603-a10a-bce6746c0456
-- title:
--   Sum estimate B: $\sum q_i^2 \ge 2c \sum q_i - c^2 b$ when $q$ has at most $b$ nonzero entries
-- statement:
--   Let $\iota$ be a finite index type and $q : \iota \to \mathbb{R}$ a family with at most $b \in \mathbb{N}$ indices where $q_i \ne 0$. Let $c \in \mathbb{R}$ be arbitrary.
--
--   **Statement.**
--   $$2c \sum_i q_i \;-\; c^2\, b \;\le\; \sum_i q_i^2 .$$
--
--   Pointwise this is just $(q_i - c)^2 \ge 0$, i.e. $q_i^2 \ge 2c\,q_i - c^2$, applied at the at most $b$ indices where $q_i \ne 0$ and summed; note that no sign hypothesis on $q$ or $c$ is needed. It is the second of the two elementary scalar estimates in the proof of the rank–trace inequality (paper reference `lem:ranktrace`). In the module `Zeta23.LinAlg.RankTrace` it is consumed directly by `RHLinalg.rank_trace_ineq`, where $q$ is the vector of positive parts of the eigenvalues of the Hermitian matrix $Q$, nonzero at most $n_+(Q) \le b$ times.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/RankTrace.lean#L85-L105, docstring tag [lem:ranktrace]

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef

open Matrix Finset
open scoped ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RHLinalg.sum_sq_lower_of_card_pos_le {q : ι → ℝ}
    {b : ℕ} (hb : #{i | q i ≠ 0} ≤ b) (c : ℝ) :
    2 * c * (∑ i, q i) - c ^ 2 * b ≤ ∑ i, (q i) ^ 2 := by sorry
