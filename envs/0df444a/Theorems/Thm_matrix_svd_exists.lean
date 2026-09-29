-- Prove2me | Theorems.Thm_matrix_svd_exists
-- name    : matrix_svd_exists
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T22:02:29.567122+00:00
-- url     : https://prove2.me/theorems/0a8925b0-8956-4886-a10c-2fcf27bb5575
-- statement:
--   **Existence of a (reduced) singular value decomposition for an arbitrary real matrix.** For every real matrix $N\in\mathbb R^{n_1\times n_2}$ there exist a rank $r\in\mathbb N$ and an SVD datum $S:\mathrm{SVD}\ N\ r$ — that is, strictly positive singular values $\sigma_1,\dots,\sigma_r>0$ together with orthonormal left vectors $u_1,\dots,u_r\in\mathbb R^{n_1}$ and orthonormal right vectors $v_1,\dots,v_r\in\mathbb R^{n_2}$ such that $N=\sum_{k=1}^r\sigma_k\,u_k v_k^\top$. This is the classical reduced SVD existence theorem: $r$ is the number of nonzero singular values, the $v_k$ are an orthonormal eigenbasis of the Gram operator $N^\top N$ restricted to its positive eigenspaces (with $\sigma_k^2$ the corresponding eigenvalue), and $u_k=\sigma_k^{-1}N v_k$. The platform `SVD` structure carries exactly this data (with `sigma_pos`, `u_orthonormal`, `v_orthonormal`, `decomp`). Proof: diagonalize the symmetric positive operator $N^\top N$ by the spectral theorem to obtain orthonormal right singular vectors and eigenvalues $\mu_k\ge0$; set $\sigma_k=\sqrt{\mu_k}$, keep only the indices with $\sigma_k>0$, define $u_k=\sigma_k^{-1}Nv_k$ (orthonormal since $\langle Nv_i,Nv_j\rangle=\langle (N^\top N)v_i,v_j\rangle=\mu_i\delta_{ij}$), and verify $N=\sum_k\sigma_k u_k v_k^\top$ from the eigenbasis reconstruction $Nx=\sum_k\langle v_k,x\rangle Nv_k$ (terms with $\sigma_k=0$ have $Nv_k=0$).
-- source:
--   Classical linear algebra (SVD existence); used as the witness builder for Candès–Recht 2009, Lemma 3.2 dual achiever (arXiv:0805.4471, p.15)

import Definitions.Def_matrix_completion_svd
open MatrixCompletion

theorem matrix_svd_exists {n1 n2 : Nat} (N : Matrix (Fin n1) (Fin n2) ℝ) : ∃ (r : Nat) (S : SVD N r), True := by sorry
