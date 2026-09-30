-- Prove2me | Theorems.Thm_XuMannorRobust_Lasso_lasso_l1_norm_bound
-- name    : XuMannorRobust.Lasso.lasso_l1_norm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:26:25.804389+00:00
-- url     : https://prove2.me/theorems/1921ed98-a6f2-4493-8444-71a42b4bc1fa
-- title:
--   Optimality bound $\|w^*\|_1 \le \frac{1}{nc}\sum_i y_i^2$ for a Lasso solution
-- statement:
--   Let $c > 0$, let $\mathbf s = ((y_1, x_1), \dots, (y_n, x_n))$ be a training set with $y_i \in \mathbb R$ and $x_i \in \mathbb R^m$, and let $w^*$ be a solution of the Lasso
--
--   $$\min_w \frac1n \sum_{i=1}^n (y_i - x_i^\top w)^2 + c\|w\|_1 .$$
--
--   Then, comparing with $w = 0$,
--
--   $$\frac1n \sum_{i=1}^n (y_i - x_i^\top w^*)^2 + c\|w^*\|_1 \le \frac1n \sum_{i=1}^n (y_i - x_i^\top 0)^2 + c\|0\|_1 = \frac1n \sum_{i=1}^n y_i^2,$$
--
--   and consequently
--
--   $$\|w^*\|_1 \le \frac{1}{nc} \sum_{i=1}^n y_i^2 .$$
--
--   This a priori bound on the size of any Lasso solution is what makes the Lasso's loss Lipschitz in the sample with a data-dependent constant (Lemma 3).
--
--   **Formalization Note** The statement is the conjunction of the three displayed facts. The factors $1/n$ and $1/(nc)$ are real divisions; for $n = 0$ both are $0$ in Lean, consistently with the fact that the only Lasso solution is then $w^* = 0$.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 419, Appendix F, proof of Lemma 3 (optimality display)

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation

namespace XuMannorRobust.Lasso

/-- **Optimality bound on the Lasso solution** (Xu & Mannor 2012, p. 419, proof of Lemma 3).
If `c > 0` and `w*` solves the Lasso (5) for the training set `s`, then its objective value is at
most that of `w = 0`, which equals `(1/n) ∑ y_i²`, and hence `‖w*‖₁ ≤ (1/(nc)) ∑ y_i²`. -/
theorem lasso_l1_norm_bound {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w) :
    lassoObjective c s w ≤ lassoObjective c s 0 ∧
    lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 ∧
    l1norm w ≤ (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by sorry

end XuMannorRobust.Lasso
