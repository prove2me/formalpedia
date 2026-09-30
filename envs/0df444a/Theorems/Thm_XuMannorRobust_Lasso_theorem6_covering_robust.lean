-- Prove2me | Theorems.Thm_XuMannorRobust_Lasso_theorem6_covering_robust
-- name    : XuMannorRobust.Lasso.theorem6_covering_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:29:52.090288+00:00
-- url     : https://prove2.me/theorems/1e76b548-76fe-4da2-9862-e8247108785e
-- title:
--   Theorem 6: a locally stable loss gives $(\mathcal N(\gamma/2, \mathcal Z, \rho), \epsilon(\mathbf s))$-robustness
-- statement:
--   Let $(\mathcal Z, \rho)$ be a metric space of samples, fix $\gamma > 0$, and let $\mathcal A : \mathcal Z^n \to \mathcal H$ be a learning algorithm with loss $l$. Recall that a set $\hat T \subseteq \mathcal Z$ is a $\gamma/2$-cover of $\mathcal Z$ if every point of $\mathcal Z$ lies within distance $\le \gamma/2$ of some point of $\hat T$, and that the covering number $\mathcal N(\gamma/2, \mathcal Z, \rho)$ is the minimal cardinality of such a cover. Suppose that for every training set $\mathbf s \in \mathcal Z^n$,
--
--   $$|l(\mathcal A_{\mathbf s}, z_1) - l(\mathcal A_{\mathbf s}, z_2)| \le \epsilon(\mathbf s) \qquad \forall z_1, z_2 :\ z_1 \in \mathbf s,\ \rho(z_1, z_2) \le \gamma,$$
--
--   and that $\mathcal N(\gamma/2, \mathcal Z, \rho) < \infty$. Then $\mathcal A$ is $(\mathcal N(\gamma/2, \mathcal Z, \rho), \epsilon(\cdot))$-robust.
--
--   The theorem turns a local stability property of the loss around training points into robustness with a number of cells given by a covering number; Examples 4–8 of the paper are all derived from it.
--
--   **Formalization Note** $\mathcal Z$ is a set `Z` in a metric space `α` with the restricted distance. The covering number is Mathlib's `Metric.coveringNumber` (closed balls, centres in `Z`, value in `ℕ∞`) at radius `Real.toNNReal (γ/2)`; since it is assumed finite, `toNat` returns its true value. In the hypothesis, $z_1$ is a training point $s_j$ and $z_2$ ranges over `Z`.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 402, Theorem 6 (with Definition 1, p. 394)

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_IsRobustOn

namespace XuMannorRobust.Lasso

/-- **Theorem 6** (Xu & Mannor 2012, p. 402). Let `Z` be a subset of a metric space `α` (the
metric of `Z` is the restriction of `dist`), and fix `γ > 0`. Suppose that for every training set
`s ∈ Zⁿ`, every training point `z₁ = s_j` and every `z₂ ∈ Z` with `dist z₁ z₂ ≤ γ`,
`|l(A_s, z₁) − l(A_s, z₂)| ≤ ε(s)`, and that the covering number `N(γ/2, Z, dist)` is finite.
Then `A` is `(N(γ/2, Z, dist), ε(·))`-robust.

`N(γ/2, Z, dist)` is Mathlib's (internal) covering number `Metric.coveringNumber`: the least
cardinality of a set of centres in `Z` such that every point of `Z` is within distance `≤ γ/2` of
some centre (Definition 1, p. 394, with the metric space of Definition 1 taken to be `Z`). -/
theorem theorem6_covering_robust {α H : Type*} [MetricSpace α] {n : ℕ} (Z : Set α)
    (l : H → α → ℝ) (A : (Fin n → α) → H) (ε : (Fin n → α) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hA : ∀ s : Fin n → α, (∀ j, s j ∈ Z) → ∀ j : Fin n, ∀ z ∈ Z,
      dist (s j) z ≤ γ → |l (A s) (s j) - l (A s) z| ≤ ε s)
    (hN : Metric.coveringNumber (Real.toNNReal (γ / 2)) Z < ⊤) :
    IsRobustOn Z l A (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat ε := by sorry

end XuMannorRobust.Lasso
