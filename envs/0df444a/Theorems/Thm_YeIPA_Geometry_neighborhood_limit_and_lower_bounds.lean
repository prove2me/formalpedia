-- Prove2me | Theorems.Thm_YeIPA_Geometry_neighborhood_limit_and_lower_bounds
-- name    : YeIPA.Geometry.neighborhood_limit_and_lower_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:57.336665+00:00
-- url     : https://prove2.me/theorems/8369553c-8592-418e-8149-8081067a3276
-- title:
--   Theorem 2.18 (ii) — limits of $\mathcal N(\eta)$ are optimal; $x_j\ge(1-\eta)x^*_j/n$ on $P^*$, $s_j\ge(1-\eta)s^*_j/n$ on $Z^*$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $n>m$, have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, suppose that both $(LP)$ $\min\{c^Tx: Ax=b,\ x\ge0\}$ and $(LD)$ $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ have interior feasible points, and let $0<\eta<1$. Let $\mathcal N(\eta)$ be the set of interior feasible triples $(x,y,s)$ with $\|Xs-\mu e\|\le\eta\mu$, $\mu=x^Ts/n$, where $\|\cdot\|$ is any function on $\mathbb R^n$ with $\|v\|\ge\|v\|_{-\infty}=|\min(0,\min_j v_j)|$ for every $v$ (for instance any $\ell_p$ norm, or the one-sided norm itself), and let $(P^*,Z^*)$ be the strict complementarity partition of $\{1,\dots,n\}$. Then:
--
--   1. Any limit point of $\mathcal N(\eta)$ as $\mu\to0$ is an optimal solution pair: if $(x^k,y^k,s^k)\in\mathcal N(\eta)$ for every $k$, $\mu^k=(x^k)^Ts^k/n\to0$ and $(x^k,y^k,s^k)\to(\bar x,\bar y,\bar s)$, then $\bar x$ is optimal for $(LP)$ and $(\bar y,\bar s)$ is optimal for $(LD)$.
--   2. For every $(x,y,s)\in\mathcal N(\eta)$,
--   $$x_j\ \ge\ \frac{(1-\eta)\,x^*_j}{n}\quad (j\in P^*),\qquad s_j\ \ge\ \frac{(1-\eta)\,s^*_j}{n}\quad (j\in Z^*),$$
--   where $x^*$ is any optimal primal solution and $(y^*,s^*)$ any optimal dual solution.
--
--   The lower bounds say that iterates in the neighbourhood keep the coordinates of the optimal partition bounded away from zero, in proportion to every optimal solution.
--
--   **Formalization Note** The book writes "‖.‖ can be any norm, or even a one-sided norm" in the definition of $\mathcal N(\eta)$ (p. 73), where $\|v\|_{-\infty}=|\min(0,\min_j v_j)|$; here $\|\cdot\|$ is any function on $\mathbb R^n$ with $\|v\|\ge\|v\|_{-\infty}$ for all $v$, which covers every $\ell_p$ norm and the one-sided norm (finding F5: for an arbitrary norm, such as $0.1\|\cdot\|_\infty$, the lower bounds of Theorem 2.18 (ii) fail). "Limit point as $\mu\to0$" is read as the limit of a convergent sequence in $\mathcal N(\eta)$ along which $\mu\to0$. The hypotheses $\operatorname{rank}A=m$ and $n>m$ are the chapter's standing assumptions (p. 48). The book gives no proof of Theorem 2.18.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 74, Theorem 2.18 (ii) (N(η) defined on p. 73)

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix Filter Topology

namespace YeIPA.Geometry

/-- Theorem 2.18 (ii) (Ye 1997, p. 74). Let `A` have rank `m`, with `n > m` (p. 48), let (LP) and (LD) both
have interior feasible points, and let `0 < η < 1`; `N(η)` is taken with any `‖.‖` that
dominates the one-sided norm `‖v‖_{−∞} = |min(0, min v)|` of p. 73 (every `ℓ_p` norm does;
FINDINGS.yaml F5: for an arbitrary norm part 2 fails).
1. Any limit point of `N(η)` as `μ → 0` is an optimal solution pair: if `(xᵏ, yᵏ, sᵏ) ∈ N(η)`,
   `μᵏ = (xᵏ)ᵀsᵏ/n → 0` and `(xᵏ, yᵏ, sᵏ) → (x̄, ȳ, s̄)`, then `x̄` is optimal for (LP) and
   `(ȳ, s̄)` is optimal for (LD).
2. For every `(x, y, s) ∈ N(η)`: `xⱼ ≥ (1 − η) x*ⱼ / n` for every `j ∈ P*` and every optimal
   primal solution `x*`, and `sⱼ ≥ (1 − η) s*ⱼ / n` for every `j ∈ Z*` and every optimal dual
   solution `(y*, s*)`. -/
theorem neighborhood_limit_and_lower_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (nrm : (Fin n → ℝ) → ℝ) (hnrm : ∀ v, negInfNorm v ≤ nrm v)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    (∀ (xk : ℕ → Fin n → ℝ) (yk : ℕ → Fin m → ℝ) (sk : ℕ → Fin n → ℝ)
        (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ),
        (∀ k, InNeighborhood A b c nrm η (xk k) (yk k) (sk k)) →
        Tendsto (fun k => mu (xk k) (sk k)) atTop (𝓝 0) →
        Tendsto xk atTop (𝓝 xbar) → Tendsto yk atTop (𝓝 ybar) → Tendsto sk atTop (𝓝 sbar) →
        IsPrimalOptimal A b c xbar ∧ IsDualOptimal A b c ybar sbar) ∧
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), InNeighborhood A b c nrm η x y s →
        (∀ xstar, IsPrimalOptimal A b c xstar → ∀ j ∈ Pstar A b c,
          (1 - η) * xstar j / n ≤ x j) ∧
        (∀ ystar sstar, IsDualOptimal A b c ystar sstar → ∀ j ∈ Zstar A b c,
          (1 - η) * sstar j / n ≤ s j)) := by sorry

end YeIPA.Geometry
