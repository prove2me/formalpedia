-- Prove2me | solution 1 for matrix_inner_tangent_normal_decomposition_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:40:06.114745+00:00
-- url     : https://prove2.me/submissions/b7f4418a-e7d5-425e-83d5-3d61e9d07f12

import Theorems.Thm_matrix_inner_tangent_normal_orthogonal_decomposition

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15 in the local copy.  The paper
introduces the orthogonal decomposition
`R^{n_1 x n_2} = T \\oplus T^\\perp`, defines `P_T` in equation (3.5), and
uses this tangent/normal decomposition in the proof of Lemma 3.1.

Reduction: use the general Frobenius inner-product decomposition into tangent
and normal components, then substitute the certificate hypothesis
`P_T Y = signMatrix S` in the tangent part.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S Y = signMatrix S →
    matrixInner Y H =
      matrixInner (signMatrix S) (tangentProjection S H) +
        matrixInner (normalProjection S Y) (normalProjection S H) := by
  intro hY
  have h := matrix_inner_tangent_normal_orthogonal_decomposition S Y H
  simpa [hY] using h
