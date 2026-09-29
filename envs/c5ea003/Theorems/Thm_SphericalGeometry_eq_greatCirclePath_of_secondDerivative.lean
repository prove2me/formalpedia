-- Prove2me | Theorems.Thm_SphericalGeometry_eq_greatCirclePath_of_secondDerivative
-- name    : SphericalGeometry.eq_greatCirclePath_of_secondDerivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T14:50:04.096692+00:00
-- url     : https://prove2.me/theorems/65b1a032-74e7-4da3-a007-938ff8428e08
-- title:
--   Solutions of $g''=-\alpha^2 g$ are great-circle paths through their initial data
-- statement:
--   Let $E$ be a real inner product space, $\alpha\neq0$, and let $g:\mathbb R\to E$ be twice differentiable and solve the harmonic-oscillator equation
--   $$g''(t)=-\alpha^2\,g(t)\qquad\text{for all }t\in\mathbb R .$$
--   Then $g$ is the great-circle path through its initial data, traversed at speed $\alpha$:
--   $$g(t)=\cos(\alpha t)\,g(0)+\sin(\alpha t)\,\frac{g'(0)}{\alpha}.$$
--
--   **Role.** This is the uniqueness half of the classical solution of the vector-valued harmonic oscillator, in the explicit form needed to recognize a curve as a parametrized ellipse. It is the last step in identifying the image of a circle under a homogeneous harmonic map: once the map is written $h(r,\theta)=r^\alpha g(\theta)$ inside an apartment, the harmonic map equation in polar coordinates becomes exactly this equation for $g$, and the conclusion is that the circle is the ellipse spanned by $g(0)$ and $g'(0)/\alpha$. Mathlib has the Picard--Lindelöf uniqueness theorem for first-order systems but no closed-form solution of the second-order equation, and nothing at all relating it to the parametrized great circle.
--
--   The proof is the conservation of energy. Subtracting the candidate solution, the difference $f$ solves the same equation with $f(0)=0$ and $f'(0)=0$, and the quantity
--   $$\Phi(t)=\langle f(t),f(t)\rangle+\alpha^{-2}\langle f'(t),f'(t)\rangle$$
--   has derivative $2\langle f,f'\rangle-2\langle f',f\rangle=0$. So $\Phi\equiv\Phi(0)=0$, and both summands being non-negative forces $\langle f,f\rangle=0$, that is $f\equiv0$.
--
--   **Formalization note.** The first and second derivatives are supplied as explicit functions together with the `HasDerivAt` statements relating them, rather than through iterated `deriv`, so that no differentiability side conditions have to be discharged at the point of use. The hypothesis $\alpha\neq0$ is needed both to normalize the second frame vector and to divide by $\alpha^2$ in the conserved quantity.
-- source:
--   Classical; the form used here is the ordinary differential equation g'' + alpha^2 g = 0 obtained from the polar form of the harmonic map equation in the proof of Theorem 3.1 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem eq_greatCirclePath_of_secondDerivative {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (alpha : ℝ) (halpha : alpha ≠ 0) (g g' g'' : ℝ → E)
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (hg' : ∀ t : ℝ, HasDerivAt g' (g'' t) t)
    (hode : ∀ t : ℝ, g'' t = -(alpha ^ 2) • g t) :
    ∀ t : ℝ, g t = greatCirclePath (g 0) (alpha⁻¹ • g' 0) (alpha * t) := by sorry

end SphericalGeometry
