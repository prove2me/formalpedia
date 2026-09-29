-- Prove2me | Theorems.Thm_rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
-- name    : rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:05:38.319762+00:00
-- url     : https://prove2.me/theorems/58edd4de-7be3-48d9-8b00-d35d29b109ee
-- statement:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), **Lemma 2** (real-valued case), the assembled lower-bound  $P(F \ge 0) \ge c^{-1}$, on the **symmetric Rademacher ($\pm 1$) fiber** `rademacherExpectation`.
--
--   This is the conditional Lemma 2 (eq. (6), p.4) content on the $\sigma$-sign Rademacher fiber: for a mean-zero sign-chaos statistic $F$ with hypercontractive control $\mathbb{E}[F^4] \le K(\mathbb{E}F^2)^2$ and $\mathbb{E}F^2 > 0$, the lower-tail probability $P(F \ge 0) = \mathbb{E}[\mathbf{1}_{\{F\ge 0\}}]$ satisfies
--   $$ P(F \ge 0) \ge \frac{1}{4K}. $$
--
--   It composes exactly two ingredients (a tracked reduction): the L4–L2–L1 moment transfer `rademacher_l2_le_l1_of_l4_le_l2sq` ($\mathbb{E}F^2 \le K(\mathbb{E}|F|)^2$) and the Paley–Zygmund positivity `rademacher_paley_zygmund_meanzero_positivity` ($(\mathbb{E}|F|)^2 \le 4\mathbb{E}[F^2]P(F\ge 0)$). Chaining: $\mathbb{E}F^2 \le 4K\,\mathbb{E}[F^2]\,P(F\ge 0)$; dividing by $\mathbb{E}F^2>0$ gives $1 \le 4K\,P(F\ge 0)$.
--
--   Rademacher-fiber analogue of `bernoulli_lower_tail_positivity_from_l4_l2_hypercontractivity`. The L4–L2 hypercontractivity hypothesis is, for degree-$\le 2$ sign chaos, exactly the Bonami inequality ($K = 81$, `rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity`). Source: de la Peña–Montgomery-Smith 1995, Lemma 2; Bonami 1970 / O'Donnell, *Analysis of Boolean Functions*, Ch. 9.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped Classical BigOperators

theorem rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
    {n₁ n₂ : ℕ} (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 < K →
    rademacherExpectation F = 0 →
    0 < rademacherExpectation (fun ε => (F ε) ^ 2) →
    rademacherExpectation (fun ε => (F ε) ^ 4) ≤
        K * (rademacherExpectation (fun ε => (F ε) ^ 2)) ^ 2 →
    (1 : ℝ) / (4 * K) ≤
      rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by sorry
