-- Prove2me | Theorems.Thm_ZORiem_RGD_theorem_3_1
-- name    : ZORiem.RGD.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:09.53062+00:00
-- url     : https://prove2.me/theorems/d35c186e-5367-4ebb-9afd-85544826adba
-- title:
--   Theorem 3.1, p. 15 — ZO-RGD: (1/(N+1)) Σ_{k≤N} E‖grad f(x_k)‖² ≤ (4/η̂)((f(x₀) − f(x*))/(N+1) + C(µ)), η̂ = 1/(2(d+4)L)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (the ambient $\mathbb R^n$) and $M\subseteq E$ a $C^1$ embedded submanifold of dimension $d$, with tangent spaces $T_xM$ and orthogonal projections $P_x$ onto them. Let $R$ be a retraction on $M$ defined on all of each $T_xM$. Let $f:E\to\mathbb R$ be differentiable with Riemannian gradient $\operatorname{grad}f(x)=P_x\nabla f(x)$, satisfying **Assumption 2.1** with a constant $L>0$:
--
--   $$\big|f(R_x(\eta))-f(x)-\langle\operatorname{grad}f(x),\eta\rangle\big|\le\frac L2\|\eta\|^2\qquad(x\in M,\ \eta\in T_xM),$$
--
--   and attaining its minimum over $M$ at some $x^*\in M$. Fix $x_0\in M$ and $\mu>0$, and run **ZO-RGD** (Algorithm 1) with the constant step size
--
--   $$\hat\eta=\frac1{2(d+4)L}:\qquad x_{k+1}=R_{x_k}\big(-\hat\eta\,g_\mu(x_k)\big),\quad g_\mu(x_k)=\frac{f(R_{x_k}(\mu u_k))-f(x_k)}{\mu}u_k,\quad u_k=P_{x_k}u_0^k,$$
--
--   where $u_0^0,u_0^1,\dots$ are independent standard Gaussian vectors of $E$. Then for every $N\ge0$,
--
--   $$\frac1{N+1}\sum_{k=0}^{N}\mathbb E\,\|\operatorname{grad}f(x_k)\|^2\le\frac4{\hat\eta}\left(\frac{f(x_0)-f(x^*)}{N+1}+C(\mu)\right),\qquad C(\mu)=\frac{\mu^2L}{16}\frac{(d+3)^3}{d+4}+\frac{\mu^2L}{16}\frac{(d+6)^3}{d+4}+\frac{\mu^2L}{16}\frac{(d+6)^3}{(d+4)^2}.$$
--
--   Here $4/\hat\eta=8(d+4)L$. The theorem is the iteration-complexity guarantee of zeroth-order Riemannian gradient descent: with two function evaluations per step, the average expected squared Riemannian gradient norm decays like $d/N$ up to a bias of order $\mu^2$, with constants that depend on the manifold dimension $d$ and not on the ambient dimension $n$.
--
--   **Formalization Note** (1) The paper prints the middle term of $C(\mu)$ without the factor $L$; that term comes from the printed Proposition 2.1(b), whose proof actually gives $L^2$, and the corrected proof gives the term stated here. (2) The draws live on the canonical product space $E^{\mathbb N}$ with the product of standard Gaussian measures, and the iterates are defined for every $k$ (the algorithm run without stopping), so $x_N$ and the telescoping through $x_{N+1}$ are meaningful. (3) The expectations are lower Lebesgue integrals of $\|\operatorname{grad}f(x_k)\|^2$ and the average is computed in $[0,\infty]$, so the bound also asserts finiteness. (4) Two technical hypotheses, true for the paper's examples, make the iterates random variables: $(x,\eta)\mapsto R_x(\eta)$ is measurable and $x\mapsto P_x$ is measurable. (5) "Smooth" $f$ is weakened to differentiable $f$. (6) The parameter choices $\mu=O(\epsilon/d^{3/2})$, $N=O(d/\epsilon^2)$ of the theorem's second sentence are an $O(\cdot)$ claim and are not formalized.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Theorem 3.1, (3.1), p. 15

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RGD_Algorithm

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace ENNReal

namespace ZORiem.RGD

/-- Theorem 3.1, (3.1), p. 15: let `M` be a `C¹` embedded submanifold of dimension `d`, `R` a global
retraction, and `f` satisfy Assumption 2.1 with constant `L > 0`, with a minimizer `x*` over `M`. Run
ZO-RGD (Algorithm 1) from `x₀ ∈ M` with smoothing `µ > 0` and step `η̂ = 1/(2(d+4)L)` on i.i.d.
standard Gaussian draws. Then for every `N`,
`(1/(N+1)) Σ_{k=0}^{N} E‖grad f(x_k)‖² ≤ (4/η̂)((f(x₀) − f(x*))/(N+1) + C(µ))`,
with `C(µ) = Cmu L µ d` (the corrected constant, see `Cmu`). -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : IsRetraction M R) (hRmeas : Measurable (Function.uncurry R))
    (hPmeas : Measurable (fun x : E => (tangentSpace M x).starProjection))
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hA21 : ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
      |f (R x η) - f x - ⟪rgrad M f x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (xstar : E) (hxstar : xstar ∈ M) (hmin : ∀ y ∈ M, f xstar ≤ f y)
    (x₀ : E) (hx₀ : x₀ ∈ M) (mu : ℝ) (hmu : 0 < mu) (N : ℕ) :
    (1 / ((N : ℝ≥0∞) + 1)) * ∑ k ∈ Finset.range (N + 1),
        ∫⁻ ω, ENNReal.ofReal
          (‖rgrad M f (iterate M R f mu (1 / (2 * ((d : ℝ) + 4) * L)) x₀ k ω)‖ ^ 2) ∂(gaussSeq E) ≤
      ENNReal.ofReal ((4 / (1 / (2 * ((d : ℝ) + 4) * L))) *
        ((f x₀ - f xstar) / ((N : ℝ) + 1) + Cmu L mu d)) := by sorry

end ZORiem.RGD
