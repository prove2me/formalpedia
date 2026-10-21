-- Prove2me | Theorems.Thm_YeIPA_Geometry_central_path_bounded
-- name    : YeIPA.Geometry.central_path_bounded
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:00.087917+00:00
-- url     : https://prove2.me/theorems/b056a3aa-3a67-40a9-9eda-e094ebf1a36c
-- title:
--   Theorem 2.17 (i) — the central path is bounded for $0<\mu\le\mu^0$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $n>m$, have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose that both $(LP)$ $\min\{c^Tx: Ax=b,\ x\ge0\}$ and $(LD)$ $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ have interior feasible points. For $\mu>0$, a central path point is a triple $(x(\mu),y(\mu),s(\mu))$ with $x(\mu)>0$, $Ax(\mu)=b$, $s(\mu)>0$, $A^Ty(\mu)+s(\mu)=c$ and $x(\mu)_js(\mu)_j=\mu$ for every $j$.
--
--   Then for every $0<\mu^0<\infty$ the set
--   $$\{(x(\mu),s(\mu)) : 0<\mu\le\mu^0,\ (x(\mu),y(\mu),s(\mu)) \text{ a central path point}\}\subset\mathbb R^n\times\mathbb R^n$$
--   is bounded.
--
--   The central path is the curve interior-point methods follow; its boundedness on $(0,\mu^0]$ is what makes limit points as $\mu\to0$ exist.
--
--   **Formalization Note** The hypotheses $\operatorname{rank}A=m$ and $n>m$ are the chapter's standing assumptions (p. 48), carried explicitly. The set ranges over all central path points with $0<\mu\le\mu^0$; by Theorem 2.16 there is exactly one pair $(x(\mu),s(\mu))$ for each $\mu$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 72, Theorem 2.17 (i)

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix

namespace YeIPA.Geometry

/-- Theorem 2.17 (i) (Ye 1997, p. 72). Let `A` have rank `m`, with `n > m` (p. 48) and let (LP) and (LD) both
have interior feasible points. For every `0 < μ⁰ < ∞` the central path points `(x(μ), s(μ))`
with `0 < μ ≤ μ⁰` form a bounded set. -/
theorem central_path_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    Bornology.IsBounded {p : (Fin n → ℝ) × (Fin n → ℝ) |
      ∃ μ : ℝ, 0 < μ ∧ μ ≤ μ₀ ∧ ∃ y : Fin m → ℝ, IsCentralPathPoint A b c μ p.1 y p.2} := by sorry

end YeIPA.Geometry
