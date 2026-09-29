-- Prove2me | Theorems.Thm_bernoulli_l2_le_l1_of_l4_le_l2sq
-- name    : bernoulli_l2_le_l1_of_l4_le_l2sq
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T06:23:19.708168+00:00
-- url     : https://prove2.me/theorems/b80931b4-5a03-4d8b-8097-aac0d3981bb4
-- statement:
--   **L4 → L2 → L1 moment-transfer (Paley–Zygmund / moment log-convexity) on the discrete Bernoulli powerset measure.** For an inclusion probability $p\in[0,1]$, a constant $K\ge 0$, and any real statistic $F$ of the Bernoulli observation set, if the fourth moment is controlled by the squared second moment, $\mathbb{E}_p[F^4]\le K\,(\mathbb{E}_p[F^2])^2$ (an $L^4$-vs-$L^2$ hypercontractivity hypothesis), then the second moment is controlled by the squared first (absolute) moment, $\mathbb{E}_p[F^2]\le K\,(\mathbb{E}_p[|F|])^2$. Equivalently $\lVert F\rVert_4\le c\lVert F\rVert_2 \Rightarrow \lVert F\rVert_2\le c^2\lVert F\rVert_1$ (with $K=c^4$). Proof by two applications of Cauchy–Schwarz on the probability measure; no fractional powers. This is the moment-interpolation device de la Peña uses to transfer the Banach-valued problem to a real-valued one in the proof of Lemma 2 and of the lower bound.
-- source:
--   de la Peña–Giné, Decoupling: From Dependence to Independence, Ch. 3; de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), transfer fact stated after eq. (13) and in the proof of Lemma 2.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_l2_le_l1_of_l4_le_l2sq
    {n₁ n₂ : ℕ} (p : ℝ) (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → 0 ≤ K →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 4) ≤
        K * (bernoulliExpectation p (fun Ω => (F Ω) ^ 2)) ^ 2 →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 2) ≤
        K * (bernoulliExpectation p (fun Ω => |F Ω|)) ^ 2 := by sorry
