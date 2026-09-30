-- Prove2me | Theorems.Thm_XuMannorRobust_Lasso_example6_lasso_robust
-- name    : XuMannorRobust.Lasso.example6_lasso_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:31:53.553589+00:00
-- url     : https://prove2.me/theorems/8cd733b6-8eab-461e-bf88-1f9deebf48ab
-- title:
--   Example 6: Lasso is $(\mathcal N(\gamma/2, \mathcal Z, \|\cdot\|_\infty), (Y(\mathbf s)/c + 1)\gamma)$-robust
-- statement:
--   Let $\mathcal Z$ be a compact subset of $\mathbb R^{m+1}$, whose points are written $z = (z^{(y)}, z^{(x)})$ with $z^{(y)} \in \mathbb R$ and $z^{(x)} \in \mathbb R^m$, and let $c > 0$. Let $\mathcal A$ be a Lasso algorithm: for every training set $\mathbf s = (s_1, \dots, s_n)$, $\mathcal A_{\mathbf s} = w$ is a solution of
--
--   $$\min_w \ \frac1n \sum_{i=1}^n \big(s_i^{(y)} - w^\top s_i^{(x)}\big)^2 + c\|w\|_1 , \tag{5}$$
--
--   and let the loss be $l(\mathcal A_{\mathbf s}, z) = |z^{(y)} - \mathcal A_{\mathbf s}(z^{(x)})| = |z^{(y)} - w^\top z^{(x)}|$. Then for every $\gamma > 0$ the Lasso is
--
--   $$\Big(\mathcal N(\gamma/2, \mathcal Z, \|\cdot\|_\infty),\ \big(Y(\mathbf s)/c + 1\big)\gamma\Big)\text{-robust}, \qquad Y(\mathbf s) = \frac1n \sum_{i=1}^n \big[s_i^{(y)}\big]^2 .$$
--
--   Together with the paper's Theorem 1 this gives a generalization bound for the Lasso that holds for every selection of a minimizer.
--
--   **Formalization Note** $\mathbb R^{m+1}$ is `ℝ × (Fin m → ℝ)`, whose Lean norm is the maximum of the absolute values of the $m+1$ coordinates, i.e. $\|\cdot\|_\infty$. The covering number is Mathlib's `Metric.coveringNumber` (closed balls, centres in $\mathcal Z$) at radius `Real.toNNReal (γ/2)`, converted to `ℕ` with `toNat`; its finiteness is not assumed but follows from compactness. The algorithm is any function returning a Lasso minimizer for every training set; $c > 0$ is assumed explicitly.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 404, Example 6 (proof in Appendix F, p. 419)

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_IsRobustOn
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
import Definitions.Def_XuMannorRobust_Lasso_LassoLoss

namespace XuMannorRobust.Lasso

/-- **Example 6 (Lasso)** (Xu & Mannor 2012, p. 404). Let `Z ⊆ ℝ × ℝ^m` (a copy of `ℝ^{m+1}`
carrying the `ℓ_∞` norm) be compact, `c > 0`, and let `A` be any algorithm that returns, for each
training set `s`, a solution `A_s` of the Lasso (5). With the loss `l(w, z) = |z^{(y)} − w^⊤ z^{(x)}|`,
`A` is `(N(γ/2, Z, ‖·‖_∞), (Y(s)/c + 1)γ)`-robust for every `γ > 0`, where
`Y(s) = (1/n) ∑_{i=1}^n [s_i^{(y)}]²`. -/
theorem example6_lasso_robust {m n : ℕ} (Z : Set (ℝ × (Fin m → ℝ))) (hZ : IsCompact Z)
    (c : ℝ) (hc : 0 < c) (A : (Fin n → ℝ × (Fin m → ℝ)) → (Fin m → ℝ))
    (hA : ∀ s, IsLassoSolution c s (A s)) (γ : ℝ) (hγ : 0 < γ) :
    IsRobustOn Z lassoLoss A (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat
      (fun s => (meanSqResponse s / c + 1) * γ) := by sorry

end XuMannorRobust.Lasso
