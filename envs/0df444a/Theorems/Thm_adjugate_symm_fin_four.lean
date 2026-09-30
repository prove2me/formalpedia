-- Prove2me | Theorems.Thm_adjugate_symm_fin_four
-- name    : adjugate_symm_fin_four
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T17:30:40.019693+00:00
-- url     : https://prove2.me/theorems/3775e4c1-36ea-4fb4-a82c-a68688000077
-- title:
--   The adjugate of a symmetric 4×4 matrix is symmetric
-- statement:
--   For real numbers $a, b, c, d, e, f, h, i, j, k$, the adjugate of the symmetric matrix
--   $$H = \begin{pmatrix} a&b&c&d\\ b&e&f&h\\ c&f&i&j\\ d&h&j&k \end{pmatrix}$$
--   is the symmetric matrix of its signed $3\times 3$ cofactors, given entry by entry in the statement. For example,
--   $$\operatorname{adj}(H)_{11} = eik - ej^2 - f^2k + 2fhj - h^2i .$$
--
--   It is a routine but frequently needed computation. It makes expressions such as the bordered form $g^{\mathsf T}\operatorname{adj}(H)\,g$ explicit polynomials in the entries, ready for direct algebraic manipulation.
--
--   **Formalization note.** Mathlib provides the $2\times 2$ and $3\times 3$ cases (`Matrix.adjugate_fin_two`, `Matrix.adjugate_fin_three`) but no $4\times 4$ formula.
-- source:
--   Standard linear algebra (adjugate of a symmetric matrix).

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- The adjugate of a symmetric `4 × 4` matrix, entrywise (cofactors). -/
theorem adjugate_symm_fin_four (a b c d e f h i j k : ℝ) :
    (!![a, b, c, d; b, e, f, h; c, f, i, j; d, h, j, k] : Matrix (Fin 4) (Fin 4) ℝ).adjugate =
      !![e*i*k - e*j^2 - f^2*k + 2*f*h*j - h^2*i, -b*i*k + b*j^2 + c*f*k - c*h*j - d*f*j + d*h*i,
          b*f*k - b*h*j - c*e*k + c*h^2 + d*e*j - d*f*h, -b*f*j + b*h*i + c*e*j - c*f*h - d*e*i + d*f^2;
        -b*i*k + b*j^2 + c*f*k - c*h*j - d*f*j + d*h*i, a*i*k - a*j^2 - c^2*k + 2*c*d*j - d^2*i,
          -a*f*k + a*h*j + b*c*k - b*d*j - c*d*h + d^2*f, a*f*j - a*h*i - b*c*j + b*d*i + c^2*h - c*d*f;
        b*f*k - b*h*j - c*e*k + c*h^2 + d*e*j - d*f*h, -a*f*k + a*h*j + b*c*k - b*d*j - c*d*h + d^2*f,
          a*e*k - a*h^2 - b^2*k + 2*b*d*h - d^2*e, -a*e*j + a*f*h + b^2*j - b*c*h - b*d*f + c*d*e;
        -b*f*j + b*h*i + c*e*j - c*f*h - d*e*i + d*f^2, a*f*j - a*h*i - b*c*j + b*d*i + c^2*h - c*d*f,
          -a*e*j + a*f*h + b^2*j - b*c*h - b*d*f + c*d*e, a*e*i - a*f^2 - b^2*i + 2*b*c*f - c^2*e] := by sorry
