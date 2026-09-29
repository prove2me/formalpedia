-- Prove2me | Theorems.Thm_schatten_norm_even_pow_eq_trace_row_gram_pow
-- name    : schatten_norm_even_pow_eq_trace_row_gram_pow
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-23T20:39:31.556296+00:00
-- url     : https://prove2.me/theorems/681846fc-cbe6-4690-9023-39eea0364adf
-- statement:
--   For a real matrix $X$ and integer $n \ge 1$, the $2n$-th power of its Schatten $2n$-norm equals the trace of the $n$-th power of the row-Gram matrix $X X^{\top}$: $$\lVert X\rVert_{S_{2n}}^{2n} = \operatorname{tr}\big((X X^{\top})^{n}\big).$$ Equivalently $\sum_k \sigma_k(X)^{2n} = \operatorname{tr}((X X^{\top})^n)$, since the squared singular values of $X$ are the eigenvalues of the Gram matrix. This is the even-integer generalization of the $q=2$ Frobenius identity schatten_norm_two_eq_frobenius (fc17d92b), and is the bridge from the Schatten even-moment to a trace, used as the engine of Buchholz's noncommutative Khintchine inequality (the K-even-id node). Source: Horn-Johnson, Matrix Analysis (2nd ed.) section 7.3 (eigenvalue power-sum equals trace of the power for symmetric PSD matrices); Buchholz, Math. Ann. 319 (2001) 1-16, section 2 (even-moment trace expansion); CR2009 (arXiv:0805.4471) section 6.1 Lemma 6.1.
-- source:
--   Horn-Johnson, Matrix Analysis 2nd ed. section 7.3; Buchholz, Math. Ann. 319 (2001) 1-16 section 2; CR2009 arXiv:0805.4471 section 6.1 Lemma 6.1

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem schatten_norm_even_pow_eq_trace_row_gram_pow (n : Nat) (hn : 1 <= n) {n1 n2 : Nat} (X : MatrixCompletion.RealMatrix n1 n2) : MatrixCompletion.schattenNorm (2 * n) X ^ (2 * n) = Matrix.trace ((X * X.transpose) ^ n) := by sorry
