-- Prove2me | Theorems.Thm_YeIPA_Geometry_central_path_converges_to_analytic_centers
-- name    : YeIPA.Geometry.central_path_converges_to_analytic_centers
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:00.624112+00:00
-- url     : https://prove2.me/theorems/ef4e73f6-9334-40a0-b13f-e5122771e40b
-- title:
--   Theorem 2.17 (iii) — the central path converges to the analytic centers of the optimal faces
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $n>m$, have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose that both $(LP)$ $\min\{c^Tx: Ax=b,\ x\ge0\}$ and $(LD)$ $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ have interior feasible points. For every $\mu>0$ let $(x(\mu),y(\mu),s(\mu))$ be a central path point: $x(\mu)>0$, $Ax(\mu)=b$, $s(\mu)>0$, $A^Ty(\mu)+s(\mu)=c$ and $x(\mu)_js(\mu)_j=\mu$ for every $j$. Let $(P^*,Z^*)$ be the strict complementarity partition of $\{1,\dots,n\}$.
--
--   Then there are $x(0)\in\mathbb R^n$ and $(y(0),s(0))\in\mathbb R^m\times\mathbb R^n$ with
--   $$x(\mu)\to x(0),\qquad s(\mu)\to s(0)\qquad (\mu\to0^+),$$
--   such that
--
--   1. $x(0)$ is optimal for $(LP)$ and $(y(0),s(0))$ is optimal for $(LD)$;
--   2. $x(0)_{P^*}$ is the analytic center of the primal optimal face $\{x: A_{P^*}x_{P^*}=b,\ x_{P^*}\ge0,\ x_{Z^*}=0\}$: $x(0)$ lies on that face, $x(0)_{P^*}>0$, and $\sum_{j\in P^*}\log x_j\le\sum_{j\in P^*}\log x(0)_j$ for every $x$ on the face with $x_{P^*}>0$;
--   3. $s(0)_{Z^*}$ is the analytic center of the dual optimal face $\{y: c_{Z^*}-A_{Z^*}^Ty\ge0,\ c_{P^*}-A_{P^*}^Ty=0\}$: $s(0)$ is the slack $c-A^Ty$ of a point of that face, $s(0)_{Z^*}>0$, and $\sum_{j\in Z^*}\log s_j\le\sum_{j\in Z^*}\log s(0)_j$ for every such slack $s$ with $s_{Z^*}>0$.
--
--   This identifies the end point of the central path: path-following interior-point methods converge not to an arbitrary optimal solution but to the maximally complementary one at the center of the optimal faces.
--
--   **Formalization Note** The central path is given as an arbitrary choice of central path points $\mu\mapsto(x(\mu),y(\mu),s(\mu))$ for $\mu>0$ (by Theorem 2.16 the pair $(x(\mu),s(\mu))$ is unique); no continuity is assumed. Only $(x(\mu),s(\mu))$ is claimed to converge, as in the book. The hypotheses $\operatorname{rank}A=m$ and $n>m$ are the chapter's standing assumptions (p. 48), carried explicitly. $P^*$ ($Z^*$) is the set of indices that are positive in the primal (dual) part of some strictly complementary pair, which Theorem 1.14 shows is the book's partition.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 72, Theorem 2.17 (iii) (partition and optimal faces p. 21)

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix Filter Topology

namespace YeIPA.Geometry

/-- Theorem 2.17 (iii) (Ye 1997, p. 72). Let `A` have rank `m`, with `n > m` (the chapter's standing
assumption, p. 48) and let (LP) and (LD) both have interior feasible points (p. 63, p. 70).
For any choice of central path points `(x(μ), y(μ), s(μ))`, `μ > 0`, the pair `(x(μ), s(μ))`
converges as `μ → 0⁺` to an optimal solution pair `(x(0), s(0))` of (LP) and (LD); moreover
`x(0)_{P*}` is the analytic center of the primal optimal face and `s(0)_{Z*}` is the analytic
center of the dual optimal face, `(P*, Z*)` the strict complementarity partition. -/
theorem central_path_converges_to_analytic_centers {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ)) :
    ∃ (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ),
      Tendsto x (𝓝[>] 0) (𝓝 x₀) ∧ Tendsto s (𝓝[>] 0) (𝓝 s₀) ∧
      IsPrimalOptimal A b c x₀ ∧ IsDualOptimal A b c y₀ s₀ ∧
      IsPrimalFaceAnalyticCenter A b c x₀ ∧ IsDualFaceAnalyticCenter A b c s₀ := by sorry

end YeIPA.Geometry
