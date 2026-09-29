-- Prove2me | Theorems.Thm_RHLinalg_rank_trace_ineq
-- name    : RHLinalg.rank_trace_ineq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:06.111426+00:00
-- url     : https://prove2.me/theorems/83dfdbc7-ab0b-47c2-9a56-96f3f85df32b
-- title:
--   Rank–trace inequality: $c\,\mathrm{tr} P - \tfrac{c^2}{4} r + 2c\,\mathrm{tr} Q - c^2 b \le \|P+Q\|_F^2$
-- statement:
--   Let $P, Q$ be $n \times n$ matrices over an `RCLike` field $\mathbb{K}$, with $P$ positive semidefinite and $Q$ Hermitian. Write $\operatorname{rtrace} M = \operatorname{Re}\operatorname{tr} M$ (for a Hermitian matrix this is the full trace), $\|M\|_F^2 = \operatorname{Re} \operatorname{tr}(M^{\mathsf H} M)$ for the squared Frobenius norm, and $n_+(Q)$ for the positive index of $Q$ (number of strictly positive eigenvalues).
--
--   **Statement.** Suppose $\operatorname{rank} P \le r$ and $n_+(Q) \le b$ for natural numbers $r, b$, and let $c > 0$ be real. Then
--   $$c \cdot \operatorname{tr} P \;-\; \frac{c^2}{4}\, r \;+\; 2c \cdot \operatorname{tr} Q \;-\; c^2\, b \;\le\; \|P + Q\|_F^2 .$$
--
--   This is the paper's rank–trace inequality (`lem:ranktrace`, equation `eq:ranktrace`): a lower bound for the Frobenius norm of $P + Q$ in terms of traces, with penalties governed by the rank of the positive semidefinite part and the positive index of the Hermitian perturbation. Its proof combines von Neumann's trace inequality (`RHLinalg.vonNeumann_trace_ineq`), the trace positivity `RHLinalg.trace_mul_nonneg_of_posSemidef`, and the two elementary sum estimates `RHLinalg.sum_sq_diff_lower` and `RHLinalg.sum_sq_lower_of_card_pos_le`.
--
--   In the module `Zeta23.LinAlg.RankTrace` this is the culminating result of the linear-algebra layer; it is consumed by `Zeta23.Assembly.seamA`, the seam where the matrix-variational estimate is stitched into the proof of Theorem A (the two-thirds critical-line zero proportion).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/RankTrace.lean#L157-L256, docstring tags [lem:ranktrace], [eq:ranktrace]

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex

open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.rank_trace_ineq {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (P + Q) := by sorry
