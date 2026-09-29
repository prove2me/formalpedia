-- Prove2me | Theorems.Thm_categorical_covariance_sandwich_shift_invariant
-- name    : categorical_covariance_sandwich_shift_invariant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T04:34:42.812974+00:00
-- url     : https://prove2.me/theorems/33cdac09-d826-41be-a445-8e6ce80aa8c7
-- title:
--   Translation invariance of a categorical covariance matrix
-- statement:
--   Let $p=(p_j)_{j\in J}$ be real weights on a finite index set with $\sum_j p_j=1$. Let $X$ be a real matrix with columns indexed by $J$, and let $c$ be a vector indexed by its rows. Define $C(p)=\operatorname{diag}(p)-pp^T$. Subtracting $c$ from every column of $X$ preserves the matrix $XC(p)X^T$:
--
--   $$
--   (X-c\mathbf 1^T)C(p)(X-c\mathbf 1^T)^T=XC(p)X^T.
--   $$
--
--   The row index set can be arbitrary; only the column index set is finite. The shift is arbitrary and need not be the weighted mean. Nonnegative weights give the familiar covariance interpretation. The algebraic identity itself requires only normalization, so signed normalized weights are permitted.
--
--   This is a finite-matrix form of the classical translation invariance of covariance. Its motivation is the matrix $X(\operatorname{diag}(p)-pp^T)X^T$ in Appendix B, equations (12)–(13), of Alswaidan and Varner, *Stochastic Attention via Langevin Dynamics on the Modern Hopfield Energy*, [arXiv:2603.06875v1](https://arxiv.org/html/2603.06875v1#A2). The displayed translation identity is an elementary derived corollary of that matrix expression, rather than a separately stated theorem in the paper. It can be applied to finite matrix data without introducing a probability measure. No assertion about the full Hopfield energy, its Hessian derivation, or its convexity is part of this theorem.
-- source:
--   Elementary derived matrix identity motivated by Abdulrahman Alswaidan and Jeffrey D. Varner, Stochastic Attention via Langevin Dynamics on the Modern Hopfield Energy, arXiv:2603.06875v1 (6 March 2026), Appendix B, printed page 12, equations (12)–(13), https://arxiv.org/html/2603.06875v1#A2. The shift identity is not stated verbatim in the source.

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

set_option autoImplicit false

theorem categorical_covariance_sandwich_shift_invariant
    {m n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (hp : ∑ j, p j = 1) (X : Matrix m n ℝ) (c : m → ℝ) :
    (X - Matrix.vecMulVec c (fun _ : n => (1 : ℝ))) *
        (Matrix.diagonal p - Matrix.vecMulVec p p) *
        (X - Matrix.vecMulVec c (fun _ : n => (1 : ℝ))).transpose =
      X * (Matrix.diagonal p - Matrix.vecMulVec p p) * X.transpose := by sorry
