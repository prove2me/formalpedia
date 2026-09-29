-- Prove2me | Theorems.Thm_trace_dilation_even_pow
-- name    : trace_dilation_even_pow
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:30:34.950475+00:00
-- url     : https://prove2.me/theorems/68317d2d-5558-47ec-92d4-3d1a29d5cd1c
-- statement:
--   **Hermitian dilation trace identity.** For a real rectangular matrix $S$, the Hermitian dilation $\mathcal{H} = \begin{pmatrix} 0 & S \\ S^\top & 0 \end{pmatrix}$ (of size $(n_1+n_2)\times(n_1+n_2)$) satisfies $\operatorname{tr}(\mathcal{H}^{2n}) = \operatorname{tr}((SS^\top)^n) + \operatorname{tr}((S^\top S)^n)$. This is the foundational identity that lets a symmetric matrix-moment engine (e.g. the Tropp/Rademacher trace-moment bound, stated for Hermitian matrices) control the rectangular Schatten moment of $S$. Proof: $\mathcal{H}^2 = \operatorname{blockdiag}(SS^\top, S^\top S)$, so by induction $\mathcal{H}^{2n} = \operatorname{blockdiag}((SS^\top)^n,(S^\top S)^n)$, and the trace of a block-diagonal matrix is the sum of the block traces.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1, Thm 6.3 / Tropp 'An Introduction to Matrix Concentration Inequalities' Sec 2.6 (Hermitian dilation). The dilation H = [[0,S],[Sᵀ,0]] is the standard symmetrization that transfers a symmetric trace-moment engine on the (n1+n2) Hermitian matrix to the rectangular Gram moments.

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
open Matrix
open scoped BigOperators

theorem trace_dilation_even_pow {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) : Matrix.trace ((Matrix.fromBlocks 0 S Sᵀ 0) ^ (2 * n)) = Matrix.trace ((S * Sᵀ) ^ n) + Matrix.trace ((Sᵀ * S) ^ n) := by sorry
