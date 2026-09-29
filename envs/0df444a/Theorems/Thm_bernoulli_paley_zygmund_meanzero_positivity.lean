-- Prove2me | Theorems.Thm_bernoulli_paley_zygmund_meanzero_positivity
-- name    : bernoulli_paley_zygmund_meanzero_positivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T06:28:16.69612+00:00
-- url     : https://prove2.me/theorems/4714fb60-590e-4992-ba30-856b82b56cbf
-- statement:
--   **Paley–Zygmund positivity (de la Peña–Montgomery-Smith Proposition 1, real-valued base case) on the discrete Bernoulli powerset measure.** For an inclusion probability $p\in[0,1]$ and a mean-zero real statistic $F$ of the Bernoulli observation set ($\mathbb{E}_p[F]=0$), the probability of nonnegativity is lower-bounded by the squared first moment over the second moment (product form, no division): $$(\mathbb{E}_p[|F|])^2 \le 4\,\mathbb{E}_p[F^2]\,\mathbb{P}_p(F\ge 0).$$ Equivalently $\mathbb{P}_p(F\ge 0)\ge (\mathbb{E}_p[|F|])^2/(4\,\mathbb{E}_p[F^2])$. Proof: mean-zero gives $\mathbb{E}|F| = 2\,\mathbb{E}[F\,\mathbf{1}_{F\ge 0}]$; then Cauchy–Schwarz with the indicator $\mathbf{1}_{F\ge 0}$ (whose square equals itself) gives $(\mathbb{E}[F\,\mathbf{1}_{F\ge 0}])^2\le \mathbb{E}[F^2]\,\mathbb{P}(F\ge 0)$. This is the Paley–Zygmund lower-tail brick consumed by de la Peña's Lemma 2 / the decoupling lower-bound proof.
-- source:
--   de la Peña–Giné, Decoupling: From Dependence to Independence, Ch. 3, Proposition 1; de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), Proposition 1 (p. 4).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_paley_zygmund_meanzero_positivity
    {n₁ n₂ : ℕ} (p : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliExpectation p F = 0 →
    (bernoulliExpectation p (fun Ω => |F Ω|)) ^ 2 ≤
      4 * bernoulliExpectation p (fun Ω => (F Ω) ^ 2) *
        bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by sorry
