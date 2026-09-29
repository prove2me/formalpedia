-- Prove2me | Definitions.Def_ConvexOptimization_quadraticForms
-- name    : ConvexOptimization_quadraticForms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T16:02:42.970482+00:00
-- url     : https://prove2.me/theorems/ab22e7b4-0197-412e-bd33-293611e74653
-- title:
--   Quadratic functions and their symmetric block matrices
-- statement:
--   The two objects on which every statement of Appendix B rests: a general quadratic function on $\mathbb{R}^n$ and the symmetric block matrix that represents it.
--
--   For a matrix $F \in \mathbb{R}^{n\times n}$, a vector $g \in \mathbb{R}^n$ and a scalar $h \in \mathbb{R}$, this module defines
--
--   $$q(x) \;=\; x^{T}Fx + 2\,g^{T}x + h \qquad\text{and}\qquad M(F,g,h) \;=\; \begin{bmatrix} F & g \\ g^{T} & h\end{bmatrix} \in \mathbb{R}^{(n+1)\times(n+1)} .$$
--
--   The factor $2$ on the linear term is the book's convention (B.1), and it is exactly what makes the two match: homogenizing the variable recovers the quadratic as a form in one more dimension,
--
--   $$q(x) \;=\; \begin{bmatrix} x \\ 1\end{bmatrix}^{T} M(F,g,h) \begin{bmatrix} x \\ 1\end{bmatrix}.$$
--
--   That identity is the whole point of pairing them. It turns a *pointwise* statement about quadratic functions into a *matrix inequality* between their blocks, which is how the S-procedure's certificate $\lambda M(F_1,g_1,h_1) \succeq M(F_2,g_2,h_2)$ becomes a semidefinite feasibility problem. Note the implication is one-way: $M \succeq 0$ forces $q \ge 0$ but not conversely, and the gap between the two is precisely what the mission's results control.
--
--   No definiteness or symmetry hypothesis is imposed on $F$ here; only its symmetric part affects the values of $q$, and the statements that need symmetry assume it.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with Mathlib's dot product `⬝ᵥ` and `Matrix.mulVec`, matching the matrix-heavy statements of Appendix B; the block matrix is `Matrix.fromBlocks` indexed by `Fin n ⊕ Unit`, the extra coordinate carrying the homogenizing $1$.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 653, Appendix B, §B.1 eq. (B.1) (the quadratic function q(x) = x'Fx + 2g'x + h and the symmetric block matrix [[F, g], [g', h]] representing it)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- The quadratic function `q(x) = xᵀFx + 2gᵀx + h` (B&V App. B, eq. (B.1)). -/
def quadForm {nn : ℕ} (F : Matrix (Fin nn) (Fin nn) ℝ)
    (g : Fin nn → ℝ) (h : ℝ) (x : Fin nn → ℝ) : ℝ :=
  x ⬝ᵥ F.mulVec x + 2 * (g ⬝ᵥ x) + h

/-- The symmetric block matrix `[[F, g], [gᵀ, h]]` associated to the quadratic
function `x ↦ xᵀFx + 2gᵀx + h` (B&V App. B). -/
def symQuadBlock {nn : ℕ} (F : Matrix (Fin nn) (Fin nn) ℝ)
    (g : Fin nn → ℝ) (h : ℝ) : Matrix (Fin nn ⊕ Unit) (Fin nn ⊕ Unit) ℝ :=
  Matrix.fromBlocks F (fun i _ => g i) (fun _ j => g j) (fun _ _ => h)

end ConvexOptimization


