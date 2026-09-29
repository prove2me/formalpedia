-- Prove2me | Theorems.Thm_det_quaternionFrame_eq_bordered
-- name    : det_quaternionFrame_eq_bordered
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-28T06:49:40.715016+00:00
-- url     : https://prove2.me/theorems/ffd56b2c-3e25-46f3-9cfe-e9e8de2e0b79
-- title:
--   Tangential Hessian in the quaternion frame is a bordered Hessian
-- statement:
--   For $g = (g_0, g_1, g_2, g_3) \in \mathbb{R}^4$ let $I, J, K$ be the quaternion matrices of Joung–van Koert (Section 2.3), so that $Ig$, $Jg$, $Kg$ span the orthogonal complement of $g$. Let $F$ be the $3 \times 4$ matrix with rows $Ig = (g_2, g_3, -g_0, -g_1)$, $Jg = (g_1, -g_0, -g_3, g_2)$ and $Kg = (-g_3, g_2, -g_1, g_0)$. Then for every symmetric $4 \times 4$ real matrix $H$,
--   $$\det\bigl(F H F^{\mathsf T}\bigr) = |g|^4 \; g^{\mathsf T} \operatorname{adj}(H)\, g .$$
--
--   When $g = \nabla K$ and $H = \operatorname{Hess} K$ for a function $K$ on $\mathbb{R}^4$, the matrix $F H F^{\mathsf T}$ is the Hessian of $K$ restricted to the tangent space of the level set, written in the frame $I\nabla K, J\nabla K, K\nabla K$. The identity turns its determinant into a bordered Hessian, since $g^{\mathsf T}\operatorname{adj}(H)\,g = -\det\begin{pmatrix} H & g \\ g^{\mathsf T} & 0 \end{pmatrix}$. This is the four-dimensional, quaternion-frame analogue of the bordered-Hessian formula for the Gauss curvature of an implicit surface (Goldman, *Curvature formulas for implicit curves and surfaces*, 2005). For a Hamiltonian, the determinant factor of the positive-tangential-Hessian (convexity) test then no longer involves the frame.
--
--   **Formalization note.** $H$ is given entrywise, $H = \begin{pmatrix} a&b&c&d\\ b&e&f&h\\ c&f&i&j\\ d&h&j&k \end{pmatrix}$, so it is symmetric by construction.
-- source:
--   Quaternion frame I, J, K from Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Section 2.3; four-dimensional analogue of the bordered-Hessian curvature formula in R. Goldman, Curvature formulas for implicit curves and surfaces, Computer Aided Geometric Design 22 (2005) 632–658.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-- In the quaternion frame `I g, J g, K g` of `ℝ⁴`, the determinant of the tangential Hessian
equals `|g|⁴ · gᵀ adj(H) g` (a bordered-Hessian identity), for every symmetric `4 × 4` matrix `H`. -/
theorem det_quaternionFrame_eq_bordered (g0 g1 g2 g3 a b c d e f h i j k : ℝ) :
    (!![g2, g3, -g0, -g1; g1, -g0, -g3, g2; -g3, g2, -g1, g0] *
        !![a, b, c, d; b, e, f, h; c, f, i, j; d, h, j, k] *
        (!![g2, g3, -g0, -g1; g1, -g0, -g3, g2; -g3, g2, -g1, g0] : Matrix (Fin 3) (Fin 4) ℝ).transpose).det
      = (![g0, g1, g2, g3] ⬝ᵥ ![g0, g1, g2, g3]) ^ 2 *
        (![g0, g1, g2, g3] ⬝ᵥ Matrix.mulVec
          (!![a, b, c, d; b, e, f, h; c, f, i, j; d, h, j, k] : Matrix (Fin 4) (Fin 4) ℝ).adjugate
            ![g0, g1, g2, g3]) := by sorry
