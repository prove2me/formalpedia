-- Prove2me | Theorems.Thm_BookSixth_rotTriple_mul_eq_one
-- name    : BookSixth.rotTriple_mul_eq_one
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-26T06:01:43.804209+00:00
-- url     : https://prove2.me/theorems/2775a585-e553-4a50-8ddb-817ccbd2c4cf
-- title:
--   Chapter 15: the threefold coordinate rotation is an orthogonal involution
-- statement:
--   Let $\theta_1,\theta_2,\theta_3$ be real angles. The product of the three coordinate-plane rotation matrices, in the order $R_{12}(t\theta_3) R_{02}(t\theta_2) R_{01}(t\theta_1)$, is its own inverse: the product squared is the identity matrix. Each rotation matrix is itself an involution, because the product of a planar rotation by $\theta$ with the same rotation by $-\theta$ is the identity, and $\cos^2\theta+\sin^2\theta=1$. Consequently the three-fold rotation is an orthogonal map of determinant one, and this is what makes it usable as the linear part of the standardising isotopy of a round circle.
-- source:
--   Component of the roundness-preserving ambient motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The matrices are from the definition module `Definitions.Def_BookSixthRotations3` (theorem id 8b9bc6db-4515-4864-bece-38016a5ce502). Each single rotation satisfies $R \cdot R = 1$ because a rotation by $\theta$ followed by a rotation by $\theta$ in the same plane is a rotation by $2\theta$, and for the matrices here the second factor is the transpose, so the product is the identity by $\cos^2\theta + \sin^2\theta = 1$. Proving this once, as a statement about the three-fold MATRIX product, is what makes the accompanying isotopy statement cheap: `Matrix.mulVec_mulVec` collapses the three-fold composition to a single matrix-vector product, and the involution then discharges the mutual-inverse conditions without unfolding three matrices inside that proof.

import Mathlib
import Definitions.Def_BookSixthRotations3
open Matrix
noncomputable section

theorem BookSixth.rotTriple_mul_eq_one (θ1 θ2 θ3 : ℝ) :
    rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
      rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 = 1 := by sorry
