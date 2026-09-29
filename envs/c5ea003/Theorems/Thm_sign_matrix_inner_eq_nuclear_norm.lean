-- Prove2me | Theorems.Thm_sign_matrix_inner_eq_nuclear_norm
-- name    : sign_matrix_inner_eq_nuclear_norm
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T20:09:13.440226+00:00
-- url     : https://prove2.me/theorems/5b7f6e91-5ee1-4058-bd16-040536ad1e6b
-- statement:
--   **The sign matrix realizes the nuclear norm of $M$ (Candès–Recht 2009, eq. (3.3), p.15).** Let $M=\sum_{k=1}^r\sigma_k u_k v_k^\top$ be a rank-$r$ SVD (encoded by `S : SVD M r`) and let $E=\operatorname{sign}(M)=\sum_k u_k v_k^\top$ be the associated sign matrix (`signMatrix S`). Then the Frobenius inner product of $E$ with $M$ equals the nuclear norm of $M$:
--   $$\langle E, M\rangle \;=\; \|M\|_*.$$
--   Indeed $\langle\sum_k u_k v_k^\top,\ \sum_\ell \sigma_\ell u_\ell v_\ell^\top\rangle=\sum_k\sigma_k$ by orthonormality of the singular vectors, and $\sum_k\sigma_k=\|M\|_*$. This is the equality case of trace duality at $A=E$, $B=M$ (so $E$ is the dual certificate of $M$, i.e. $E\in\partial\|M\|_*$). Proving it on the platform requires identifying the user-supplied singular values `S.sigma` with the abstract singular values used by `nuclearNorm` (`LinearMap.singularValues`), i.e. uniqueness of singular values.
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem sign_matrix_inner_eq_nuclear_norm {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) : matrixInner (signMatrix S) M = nuclearNorm M := by sorry
