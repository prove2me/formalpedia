-- Prove2me | Theorems.Thm_rademacher_l2_le_l1_of_l4_le_l2sq
-- name    : rademacher_l2_le_l1_of_l4_le_l2sq
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:02:20.800307+00:00
-- url     : https://prove2.me/theorems/a4c5f467-513b-456a-90a5-2f94ff8db294
-- statement:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), the L4 → L2 → L1 moment-transfer device from the proof of **Lemma 2**, stated on the **symmetric Rademacher ($\pm 1$) fiber** `rademacherExpectation` (the uniform $(1/2)^N$ measure on sign assignments).
--
--   For any real statistic $F$ of the sign configuration and any $K \ge 0$, the hypercontractive control $\mathbb{E}[F^4] \le K\,(\mathbb{E}[F^2])^2$ implies the L2–L1 control $\mathbb{E}[F^2] \le K\,(\mathbb{E}|F|)^2$. Squaring the moment form, this is dlP–MS Lemma 2's line $\|\xi\|_4 \le c\|\xi\|_2 \Rightarrow \|\xi\|_2 \le c^2\|\xi\|_1$ with $K = c^4$.
--
--   The proof is two applications of Cauchy–Schwarz on the probability measure: $(\mathbb{E}F^2)^2 \le (\mathbb{E}|F|)(\mathbb{E}|F|^3)$ and $(\mathbb{E}|F|^3)^2 \le (\mathbb{E}F^2)(\mathbb{E}F^4)$, combined with the hypothesis. The uniform sign weights are unconditionally nonnegative and sum to $1$ by the binomial theorem, so no $p\in[0,1]$ hypothesis is needed (unlike the Bernoulli analogue).
--
--   This is the Rademacher-fiber analogue of `bernoulli_l2_le_l1_of_l4_le_l2sq`; it is the more source-faithful form, since dlP–MS Lemma 2 and the Bonami–Beckner inequality are naturally stated on the $\pm 1$ cube. Source: de la Peña–Montgomery-Smith 1995, Lemma 2; Bonami 1970 / O'Donnell, *Analysis of Boolean Functions*, Ch. 9.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped Classical BigOperators

theorem rademacher_l2_le_l1_of_l4_le_l2sq
    {n₁ n₂ : ℕ} (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ K →
    rademacherExpectation (fun ε => (F ε) ^ 4) ≤
        K * (rademacherExpectation (fun ε => (F ε) ^ 2)) ^ 2 →
    rademacherExpectation (fun ε => (F ε) ^ 2) ≤
        K * (rademacherExpectation (fun ε => |F ε|)) ^ 2 := by sorry
