-- Prove2me | Theorems.Thm_TrigPolynomial_coeffs_eq_zero_of_const_on_interval
-- name    : TrigPolynomial.coeffs_eq_zero_of_const_on_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T12:37:13.232096+00:00
-- url     : https://prove2.me/theorems/a12b8f9e-ce05-49d0-9a0d-872c26755dcf
-- title:
--   A single-frequency trigonometric polynomial constant on an interval vanishes
-- statement:
--   If a trigonometric polynomial of a single nonzero frequency is constant on an interval,
--   $$A\cos(2\alpha\theta)+B\sin(2\alpha\theta)=c\qquad\text{for }|\theta-\theta_0|<\delta,\ \alpha\neq0,$$
--   then all three constants vanish: $A=B=c=0$.
--
--   **Role.** A rigidity statement in the shape the theory needs it. The squared distance from a homogeneous harmonic map's circle image to the cone point has exactly this form, with $A,B$ determined by the frame of the apartment the arc lies in; asserting that this distance is *constant* — the hypothesis that separates the two branches of the order dichotomy — therefore forces the frame to be orthogonal with both vectors of the same length. Without a statement of this kind, the constant-distance hypothesis could not be converted into information about the frame.
--
--   **Proof.** Write $f(\theta)$ for the left-hand side. On the interval $f$ is constant, so $f'$ vanishes there, and hence $f''$ vanishes at the centre. Since $f''=-(2\alpha)^2 f$, and $f(\theta_0)=c$, this gives $(2\alpha)^2c=0$, so $c=0$ because $\alpha\neq0$. Now $f(\theta_0)=0$ and $f'(\theta_0)=0$ read
--   $$A\cos u+B\sin u=0,\qquad -A\sin u+B\cos u=0,\qquad u=2\alpha\theta_0,$$
--   a linear system in $(A,B)$ whose determinant is $\cos^2u+\sin^2u=1$; hence $A=B=0$.
--
--   **Formalization note.** That $f'$ vanishes on the interval is obtained pointwise: each point of an open interval on which $f$ is constant has a neighbourhood inside it, so $f$ agrees with a constant near that point, and uniqueness of the derivative gives $f'=0$ there. Applying the same reasoning to $f'$ at the centre gives $f''(\theta_0)=0$.
-- source:
--   The rigidity step separating the two branches of the order dichotomy in Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Mathlib

namespace TrigPolynomial

theorem coeffs_eq_zero_of_const_on_interval
    (A B alpha c theta0 delta : ℝ) (halpha : alpha ≠ 0) (hdelta : 0 < delta)
    (h : ∀ theta : ℝ, |theta - theta0| < delta →
      A * Real.cos (2 * alpha * theta)
        + B * Real.sin (2 * alpha * theta) = c) :
    A = 0 ∧ B = 0 ∧ c = 0 := by sorry

end TrigPolynomial
