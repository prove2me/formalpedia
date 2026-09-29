-- Prove2me | Theorems.Thm_matrix_trace_duality_inequality
-- name    : matrix_trace_duality_inequality
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T20:08:15.295005+00:00
-- url     : https://prove2.me/theorems/8cdc73ca-52b9-4c4c-8956-e2d787701754
-- statement:
--   **Trace duality (von Neumann inequality), Candès–Recht 2009, Lemma 3.2, first part (arXiv:0805.4471, p.15).** For any two real matrices $A,B\in\mathbb R^{n_1\times n_2}$, the Frobenius (trace) inner product is bounded by the product of the spectral (operator) norm of $A$ and the nuclear norm of $B$:
--   $$\langle A,B\rangle \;\le\; \|A\|\,\|B\|_*.$$
--   Here $\langle A,B\rangle=\sum_{i,j}A_{ij}B_{ij}=\operatorname{tr}(A^\top B)$ (`matrixInner`), $\|A\|$ is the operator norm (`spectralNorm`, the largest singular value), and $\|B\|_*=\sum_k\sigma_k(B)$ is the nuclear norm (`nuclearNorm`, the sum of singular values). This is the statement that the nuclear and spectral norms are dual to one another. It follows from the von Neumann trace inequality $\operatorname{tr}(A^\top B)\le\sum_k\sigma_k(A)\sigma_k(B)$ together with $\sigma_k(A)\le\|A\|$; equivalently, writing $B=\sum_k\sigma_k(B)\,u_k v_k^\top$ in its SVD, $\langle A,B\rangle=\sum_k\sigma_k(B)\,(u_k^\top A v_k)$ and $|u_k^\top A v_k|\le\|A\|$ for unit vectors $u_k,v_k$.
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) : matrixInner A B ≤ spectralNorm A * nuclearNorm B := by sorry
