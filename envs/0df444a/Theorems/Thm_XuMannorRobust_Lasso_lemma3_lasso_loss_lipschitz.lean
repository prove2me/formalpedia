-- Prove2me | Theorems.Thm_XuMannorRobust_Lasso_lemma3_lasso_loss_lipschitz
-- name    : XuMannorRobust.Lasso.lemma3_lasso_loss_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:28:00.862691+00:00
-- url     : https://prove2.me/theorems/5d67def6-bc72-47c1-9a7f-b8534e3f3a15
-- title:
--   Lemma 3: the Lasso's loss is $(\frac{1}{nc}\sum_i [s_i^{(y)}]^2 + 1)$-Lipschitz in $\|\cdot\|_\infty$
-- statement:
--   Let $c > 0$, let $\mathbf s = (s_1, \dots, s_n)$ be a training set of samples $s_i = (s_i^{(y)}, s_i^{(x)}) \in \mathbb R \times \mathbb R^m$, and let $w^*(\mathbf s)$ be a solution of the Lasso (5) for $\mathbf s$. With the absolute loss $l(w, z) = |z^{(y)} - w^\top z^{(x)}|$, for all $z_a, z_b \in \mathbb R^{m+1}$,
--
--   $$\big|l(w^*(\mathbf s), z_a) - l(w^*(\mathbf s), z_b)\big| \le \left[\frac{1}{nc} \sum_{i=1}^n \big[s_i^{(y)}\big]^2 + 1\right] \|z_a - z_b\|_\infty .$$
--
--   The loss of the learned Lasso predictor is thus Lipschitz in the test sample, with a constant depending only on the responses of the training set. Combined with Theorem 6 it yields the robustness of the Lasso (Example 6).
--
--   **Formalization Note** A sample is a pair in `ℝ × (Fin m → ℝ)`; Lean's norm on this product is the maximum of the absolute values of all $m+1$ coordinates, which is exactly $\|\cdot\|_\infty$ on $\mathbb R^{m+1}$. The points $z_a, z_b$ range over the whole space. $c > 0$ is assumed explicitly (the paper treats $c\|w\|_1$ as a penalty). For $n = 0$ the factor $1/(nc)$ is $0$ in Lean.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 419, Appendix F, Lemma 3

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
import Definitions.Def_XuMannorRobust_Lasso_LassoLoss

namespace XuMannorRobust.Lasso

/-- **Lemma 3** (Xu & Mannor 2012, p. 419). If `c > 0` and `w*(s)` solves the Lasso (5) for the
training set `s`, then for all `z_a, z_b ∈ ℝ × ℝ^m`,
`|l(w*(s), z_a) − l(w*(s), z_b)| ≤ [(1/(nc)) ∑_{i=1}^n (s_i^{(y)})² + 1] ‖z_a − z_b‖_∞`.
The norm on `ℝ × (Fin m → ℝ)` is Lean's product norm, the maximum of the absolute values of all
`m + 1` coordinates, i.e. the `ℓ_∞` norm on `ℝ^{m+1}`. -/
theorem lemma3_lasso_loss_lipschitz {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w)
    (za zb : ℝ × (Fin m → ℝ)) :
    |lassoLoss w za - lassoLoss w zb| ≤
      ((1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 + 1) * ‖za - zb‖ := by sorry

end XuMannorRobust.Lasso
