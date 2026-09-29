-- Prove2me | Theorems.Thm_HarmonicOscillator_of_polarHarmonic
-- name    : HarmonicOscillator.of_polarHarmonic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T02:23:26.927422+00:00
-- url     : https://prove2.me/theorems/0bc1ea9f-748f-4884-8521-e3d1d7c5dcbb
-- title:
--   A homogeneous harmonic function in polar coordinates obeys $g''+\alpha^2g=0$
-- statement:
--   Let $E$ be a real normed space, $\alpha\in\mathbb R$, and let $g:\mathbb R\to E$ be twice differentiable. Consider the function of polar coordinates
--
--   $$
--   w(r,\theta)=r^{\alpha}\,g(\theta),\qquad r>0,
--   $$
--
--   and suppose it is harmonic, that is, it satisfies the Laplace equation in polar coordinates
--
--   $$
--   \frac{\partial^2 w}{\partial r^2}+\frac1r\frac{\partial w}{\partial r}+\frac1{r^2}\frac{\partial^2 w}{\partial\theta^2}=0 .
--   $$
--
--   Then $g$ satisfies the harmonic oscillator equation
--
--   $$
--   g''=-\alpha^2\,g .
--   $$
--
--   **Role.** This is separation of variables in the only case it is needed: a function that is *already known* to be homogeneous of degree $\alpha$ in the radial variable, so that the angular profile $g$ is the sole remaining unknown. Differentiating $r^\alpha$ twice contributes $\alpha(\alpha-1)r^{\alpha-2}g$ and $\alpha r^{\alpha-2}g$ to the first two terms, and the angular term contributes $r^{\alpha-2}g''$; the common factor $r^{\alpha-2}$ is nonzero for $r>0$, and what is left is $\alpha^2g+g''=0$.
--
--   In the analysis of a homogeneous harmonic map into a Euclidean building this is the step that converts a partial differential equation on a planar domain into an ordinary differential equation on the circle. It applies to each apartment separately, since inside an apartment the map takes values in a Euclidean space and is harmonic there in the ordinary sense; and its conclusion, combined with the solution formula for the oscillator, is what produces the representation $g(\theta)=\mathbf v_1\cos(\alpha\theta)+\mathbf v_2\sin(\alpha\theta)$.
--
--   **Formalization Note.** The partial derivatives are supplied as functions together with the hypotheses identifying them, rather than through a differential-geometric Laplacian, so that the statement is exactly the displayed polar equation and nothing more. The radial hypotheses are imposed only for $r>0$, where $r^\alpha$ is differentiable for arbitrary real $\alpha$.
-- source:
--   The substitution step in the proof of Theorem 3.1 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608 ("Writing w(r,theta) = r^alpha g(theta) and setting r = 1, we obtain a differential equation for g"). Mathlib has no Laplacian in polar coordinates and no separation of variables.

import Mathlib

namespace HarmonicOscillator

theorem of_polarHarmonic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha : ℝ) (g g' g'' : ℝ → E)
    (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (wr wrr wt wtt : ℝ → ℝ → E)
    (hwr : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s ^ alpha • g t) (wr r t) r)
    (hwrr : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => wr s t) (wrr r t) r)
    (hwt : ∀ r t : ℝ, HasDerivAt (fun u : ℝ => r ^ alpha • g u) (wt r t) t)
    (hwtt : ∀ r t : ℝ, HasDerivAt (fun u : ℝ => wt r u) (wtt r t) t)
    (hharm : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      wrr r t + r⁻¹ • wr r t + (r ^ 2)⁻¹ • wtt r t = 0) :
    ∀ t : ℝ, g'' t = -(alpha ^ 2) • g t := by sorry

end HarmonicOscillator
