-- Prove2me | Theorems.Thm_bernoulli_lower_tail_positivity_from_l4_l2_hypercontractivity
-- name    : bernoulli_lower_tail_positivity_from_l4_l2_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T01:47:54.819591+00:00
-- url     : https://prove2.me/theorems/2edc63a6-0426-4ddb-acf4-3b13a3f6fbc2
-- statement:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), the real-valued **Lemma 2** lower bound assembled from its two scaffolding ingredients.
--
--   For a mean-zero statistic $F$ on the discrete Bernoulli powerset measure (inclusion probability $p\in[0,1]$) satisfying the L⁴↔L² hypercontractivity hypothesis $\mathbb E[F^4]\le K\,(\mathbb E[F^2])^2$ with $K>0$, and with non-degenerate second moment $\mathbb E[F^2]>0$, the lower tail is bounded below by a fixed fraction:
--   $$\Pr(F\ge 0) \ge \frac{1}{4K}.$$
--
--   This is exactly de la Peña's Lemma 2 specialised to a real statistic: $\Pr(F\ge0)\ge c^{-1}$ with $c=4K$. It composes the **L⁴→L²→L¹ moment transfer** ($\mathbb E[F^2]\le K(\mathbb E|F|)^2$, node `bernoulli_l2_le_l1_of_l4_le_l2sq`) with **Proposition 1 / Paley–Zygmund positivity** ($(\mathbb E|F|)^2\le 4\,\mathbb E[F^2]\,\Pr(F\ge0)$, node `bernoulli_paley_zygmund_meanzero_positivity`): chaining gives $\mathbb E[F^2]\le 4K\,\mathbb E[F^2]\,\Pr(F\ge0)$ and division by $\mathbb E[F^2]>0$ yields the claim.
--
--   The only ingredient supplied as a HYPOTHESIS (not derived here) is the L⁴↔L² hypercontractivity constant $K$ — for the $\sigma$-randomized multilinear chaos this is Kwapıeń–Szulga 1991 (Ann. Probab. 19, 369–379, eq. 1.4), the genuinely Mathlib-absent step. For the order-2 symmetric ($p=1/2$) case it is the proved node `centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity` with $K=3$.
-- source:
--   de la Peña–Montgomery-Smith 1995, Ann. Probab. 23(1), 806–816 (arXiv:math/9309211), Lemma 2 / Proposition 1; de la Peña–Giné, Decoupling, Ch. 3.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.Order.Field.Basic
open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_lower_tail_positivity_from_l4_l2_hypercontractivity
    {n₁ n₂ : ℕ} (p : ℝ) (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → 0 < K →
    bernoulliExpectation p F = 0 →
    0 < bernoulliExpectation p (fun Ω => (F Ω) ^ 2) →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 4) ≤
        K * (bernoulliExpectation p (fun Ω => (F Ω) ^ 2)) ^ 2 →
    (1 : ℝ) / (4 * K) ≤ bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by sorry
