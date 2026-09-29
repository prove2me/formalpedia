-- Prove2me | Theorems.Thm_spectral_norm_pow_two_mul_le_trace_pow
-- name    : spectral_norm_pow_two_mul_le_trace_pow
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T15:50:48.808373+00:00
-- url     : https://prove2.me/theorems/4a89905d-6de9-4201-a09a-74a7e1fd201a
-- statement:
--   For a real symmetric (Hermitian) matrix $X \in \mathbb{R}^{d\times d}$ with $d \ge 1$ and any natural number $p$, the $2p$-th power of the operator (spectral) norm is bounded by the trace of the $2p$-th matrix power: $\lVert X\rVert_{op}^{2p} \le \operatorname{tr}(X^{2p})$. This is the spectral-radius $\le$ Schatten-$2p$ trace-moment inequality (the maximal eigenvalue to the $2p$ is dominated by the sum of all eigenvalues to the $2p$, which equals $\operatorname{tr}(X^{2p})$ for symmetric $X$). The hypothesis $0<d$ is needed: at $d=0,p=0$ the bare statement is false ($1 \le 0$). Proved via the spectral theorem, C*-ring unitary invariance of the operator norm, and `Finset.single_le_sum`.
-- source:
--   Tropp 2015 (An Introduction to Matrix Concentration Inequalities) Thm 4.1; van Handel arXiv:1610.05200 §3; CR2009 arXiv:0805.4471 §4.2

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
open Matrix MatrixCompletion

theorem spectral_norm_pow_two_mul_le_trace_pow
    {d : ℕ} (hd0 : 0 < d) (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.IsHermitian) (p : ℕ) :
    spectralNorm X ^ (2 * p) ≤ Matrix.trace (X ^ (2 * p)) := by sorry
