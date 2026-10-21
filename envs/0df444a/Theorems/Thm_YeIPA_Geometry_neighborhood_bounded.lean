-- Prove2me | Theorems.Thm_YeIPA_Geometry_neighborhood_bounded
-- name    : YeIPA.Geometry.neighborhood_bounded
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:00.012677+00:00
-- url     : https://prove2.me/theorems/15a53ffe-2d14-401b-98dd-bf5edf8ebe09
-- title:
--   Theorem 2.18 (i) — $\mathcal N(\eta)\cap\{x^Ts\le n\mu^0\}$ is bounded
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $n>m$, have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose that both $(LP)$ $\min\{c^Tx: Ax=b,\ x\ge0\}$ and $(LD)$ $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ have interior feasible points. For $0<\eta<1$ let
--   $$\mathcal N(\eta)=\Big\{(x,y,s):\ Ax=b,\ x>0,\ A^Ty+s=c,\ s>0,\ \|Xs-\mu e\|\le\eta\mu,\ \mu=\tfrac{x^Ts}{n}\Big\},$$
--   where $X=\operatorname{diag}(x)$, $e$ is the all-ones vector and $\|\cdot\|$ is any function on $\mathbb R^n$ with $\|v\|\ge\|v\|_{-\infty}=|\min(0,\min_j v_j)|$ for every $v$ (for instance any $\ell_p$ norm, or the one-sided norm itself).
--
--   Then for every real $\mu^0$ the set
--   $$\mathcal N(\eta)\cap\{(x,y,s): x^Ts\le n\mu^0\}\subset\mathbb R^n\times\mathbb R^m\times\mathbb R^n$$
--   is bounded.
--
--   Path-following algorithms keep their iterates in $\mathcal N(\eta)$ while driving $\mu$ down; this statement guarantees that such iterates stay in a bounded region.
--
--   **Formalization Note** The book writes "‖.‖ can be any norm, or even a one-sided norm" in the definition of $\mathcal N(\eta)$ (p. 73), where $\|v\|_{-\infty}=|\min(0,\min_j v_j)|$; here $\|\cdot\|$ is any function on $\mathbb R^n$ with $\|v\|\ge\|v\|_{-\infty}$ for all $v$, which covers every $\ell_p$ norm and the one-sided norm (finding F5: for an arbitrary norm, such as $0.1\|\cdot\|_\infty$, the lower bounds of Theorem 2.18 (ii) fail). The hypotheses $\operatorname{rank}A=m$ and $n>m$ are the chapter's standing assumptions (p. 48); the rank is needed for the boundedness of the $y$-component (finding F7; the item `YeIPA.Geometry.neighborhood_bounded_probe` drops it).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 74, Theorem 2.18 (i) (N(η) defined on p. 73)

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix

namespace YeIPA.Geometry

/-- Theorem 2.18 (i) (Ye 1997, p. 74). Let `A` have rank `m`, with `n > m` (p. 48), let (LP) and (LD) both
have interior feasible points, and let `0 < η < 1`. For every `μ⁰ < ∞` the set
`N(η) ∩ {(x, y, s) : xᵀs ≤ nμ⁰}` is bounded. `N(η)` is taken with any `‖.‖` that dominates the one-sided norm
`‖v‖_{−∞} = |min(0, min v)|` of p. 73 (every `ℓ_p` norm does; FINDINGS.yaml F5). -/
theorem neighborhood_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (nrm : (Fin n → ℝ) → ℝ) (hnrm : ∀ v, negInfNorm v ≤ nrm v)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (μ₀ : ℝ) :
    Bornology.IsBounded {p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) |
      InNeighborhood A b c nrm η p.1 p.2.1 p.2.2 ∧ p.1 ⬝ᵥ p.2.2 ≤ n * μ₀} := by sorry

end YeIPA.Geometry
