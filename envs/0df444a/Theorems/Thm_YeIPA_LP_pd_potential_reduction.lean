-- Prove2me | Theorems.Thm_YeIPA_LP_pd_potential_reduction
-- name    : YeIPA.LP.pd_potential_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:24.121764+00:00
-- url     : https://prove2.me/theorems/600eb2b6-2f36-49d3-b04d-399546aaf83d
-- title:
--   Theorem 4.9 — one potential-reduction step lowers $\psi_{n+\sqrt n}$ by a constant $\delta>1/20$
-- statement:
--   Consider standard-form linear programs (LP) $\min\{c^Tx: Ax=b,\ x\ge0\}$ and (LD) $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ with $A\in\mathbb R^{m\times n}$ of rank $m$, $n\ge1$, $b\ne0$, both having interior feasible points. Let
--   $$\psi_{n+\rho}(x,s)=(n+\rho)\log(x^Ts)-\sum_{j=1}^n\log(x_js_j).$$
--   There is a constant $\delta>1/20$ such that the following holds for every such problem and every $(x^k,y^k,s^k)\in\mathring{\mathcal F}$. Let $\rho=\sqrt n$, $z^k=b^Ty^k$, let
--   $$x^{k+1}=x^k-\alpha\frac{X^kp^k}{\|p^k\|}\quad(4.10),\qquad p^k=(I-X^kA^T(A(X^k)^2A^T)^{-1}AX^k)X^k\Big(\frac{n+\rho}{c^Tx^k-z^k}c-(X^k)^{-1}e\Big),$$
--   with $\alpha=0.3$, and let $y^{k+1}=y(z^k)$ and $s^{k+1}=s(z^k)=c-A^Ty(z^k)$ be given by (4.12)–(4.13). Then
--   $$\psi_{n+\rho}(x^{k+1},s^k)\le\psi_{n+\rho}(x^k,s^k)-\delta\qquad\text{or}\qquad\psi_{n+\rho}(x^k,s^{k+1})\le\psi_{n+\rho}(x^k,s^k)-\delta.$$
--
--   This is the central estimate of the primal-dual potential-reduction algorithm (Algorithm 4.3): the primal-dual potential can be reduced by a constant no matter where the iterate is, which yields the $O(\sqrt n\log((x^0)^Ts^0/\epsilon))$ iteration bound of Corollary 4.10.
--
--   **Formalization Note** The step length $\alpha$ in (4.10) is not fixed in the theorem's sentence; the proof fixes $\alpha=.3$ (together with $\eta=.43$ in the case split (4.14), which does not enter the statement), and the statement is made for that step. The constant $\delta$ is quantified before the problem data, so it is one number valid for all $m$, $n$, $A$, $b$, $c$ and iterates, as in the book. The standing assumptions (rank $m$, interior points, p. 63; $b\ne0$, p. 109) and $n\ge1$ are explicit hypotheses. When $p^k=0$ the book's step is undefined and Lean's $x^{k+1}$ equals $x^k$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 124, Theorem 4.9

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix

namespace YeIPA.LP

/-- Theorem 4.9 (Ye 1997, p. 124). There is a constant `δ > 1/20` such that the following holds
for every standard-form LP satisfying the standing assumptions (p. 63) and every
`(xᵏ, yᵏ, sᵏ) ∈ F̊`. Let `ρ = √n`, `zᵏ = bᵀyᵏ`, let `xᵏ⁺¹` be given by (4.10) with the step
length `α = .3` that the proof fixes (p. 125), and let `yᵏ⁺¹ = y(zᵏ)` (4.13) and
`sᵏ⁺¹ = s(zᵏ)` (4.12). Then either `ψ_{n+ρ}(xᵏ⁺¹, sᵏ) ≤ ψ_{n+ρ}(xᵏ, sᵏ) − δ` or
`ψ_{n+ρ}(xᵏ, sᵏ⁺¹) ≤ ψ_{n+ρ}(xᵏ, sᵏ) − δ`. -/
theorem pd_potential_reduction :
    ∃ δ : ℝ, 1 / 20 < δ ∧
      ∀ (m n : ℕ), 0 < n → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
        StandingAssumptions A b c →
        ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), IsInteriorFeasible A b c x y s →
          pdPotential (Real.sqrt n) (primalStep A c (Real.sqrt n) (3 / 10) x (b ⬝ᵥ y)) s ≤
              pdPotential (Real.sqrt n) x s - δ ∨
            pdPotential (Real.sqrt n) x (sOf A b c (Real.sqrt n) x (b ⬝ᵥ y)) ≤
              pdPotential (Real.sqrt n) x s - δ := by sorry

end YeIPA.LP
