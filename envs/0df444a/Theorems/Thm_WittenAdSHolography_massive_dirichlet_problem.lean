-- Prove2me | Theorems.Thm_WittenAdSHolography_massive_dirichlet_problem
-- name    : WittenAdSHolography.massive_dirichlet_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:36:43.645228+00:00
-- url     : https://prove2.me/theorems/d18dd097-b5d8-490a-8927-0182d988f12c
-- title:
--   Eq. (2.41): the massive Poisson integral solves $\Delta_g\varphi=m^2\varphi$ with $\varphi\sim x_0^{d-\Delta}\varphi_0$
-- statement:
--   Let $d\ge0$ be an integer and $m^2\in\mathbb R$ with $m^2>-d^2/4$, and put
--   $$\Delta=\tfrac12\big(d+\sqrt{d^2+4m^2}\big).$$
--   There is a constant $c>0$ such that for every bounded continuous $\varphi_0:\mathbb R^d\to\mathbb R$ the function
--   $$\varphi(x_0,x)=c\int_{\mathbb R^d}\frac{x_0^{\Delta}}{(x_0^2+|x-x'|^2)^{\Delta}}\,\varphi_0(x')\,dx'$$
--   satisfies
--
--   1. $\varphi$ is $C^2$ on the upper half space $\{x_0>0\}$ and solves the massive wave equation $\Delta_g\varphi=m^2\varphi$ for the hyperbolic metric $x_0^{-2}(dx_0^2+\sum_idx_i^2)$;
--   2. for every $x\in\mathbb R^d$, $\displaystyle\lim_{x_0\to0^+}x_0^{\Delta-d}\,\varphi(x_0,x)=\varphi_0(x)$, i.e. $\varphi$ behaves like $x_0^{d-\Delta}\varphi_0(x)=x_0^{-\lambda_+}\varphi_0(x)$ at the boundary.
--
--   This is the boundary-value problem through which Witten identifies the boundary datum of a mass-$m$ scalar with a conformal density, and hence the dual operator's dimension with $\Delta$.
--
--   **Formalization Note** The endpoint $m^2=-d^2/4$ ($\Delta=d/2$) is excluded because the kernel is then not integrable. Boundary data are bounded continuous functions.
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, pp. 20-21, Section 2.5, eqs. (2.36), (2.41), (2.43)-(2.44)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.massive_dirichlet_problem (d : ℕ) (msq : ℝ) (hm : -((d : ℝ) ^ 2) / 4 < msq) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ₀ : Bdry d → ℝ, Continuous φ₀ → (∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) →
      IsMassiveSolution d msq (fun x₀ x => c * poissonIntegral (confDim d msq) φ₀ x₀ x) ∧
      ∀ x : Bdry d, Tendsto
        (fun x₀ : ℝ => x₀ ^ (confDim d msq - d) * (c * poissonIntegral (confDim d msq) φ₀ x₀ x))
        (𝓝[>] 0) (𝓝 (φ₀ x)) := by sorry
