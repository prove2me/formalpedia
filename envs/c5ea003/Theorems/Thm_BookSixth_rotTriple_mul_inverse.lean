-- Prove2me | Theorems.Thm_BookSixth_rotTriple_mul_inverse
-- name    : BookSixth.rotTriple_mul_inverse
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-26T06:42:01.73199+00:00
-- url     : https://prove2.me/theorems/7d284dcc-d651-41f2-a942-6bd495e15fa0
-- title:
--   Chapter 15: the threefold coordinate rotation is orthogonal, with inverse given by the opposite angles
-- statement:
--   Let $\theta_1,\theta_2,\theta_3$ be real angles. The product of the three coordinate-plane rotation matrices, in the order $R_{12}(\theta_3) R_{02}(\theta_2) R_{01}(\theta_1)$, is a product of orthogonal matrices and is therefore orthogonal; explicitly, multiplying it by the same product taken at the OPPOSITE angles, $R_{12}(-\theta_3) R_{02}(-\theta_2) R_{01}(-\theta_1)$, gives the identity. A planar rotation by $\theta$ is inverted by a rotation by $-\theta$, because the product is a rotation by $0$ and $\cos^2\theta+\sin^2\theta=1$; products of invertibles are invertible, so the three-fold product has the stated inverse. This is what makes the three-fold rotation usable as the linear part of the standardising isotopy of a round circle. Note that the inverse is NOT the product at the same angles: $R(\theta) R(\theta)$ is a rotation by $2\theta$, which is the identity only when $\theta$ is a multiple of $\pi$.
-- source:
--   Component of the roundness-preserving ambient motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The matrices are from the definition module `Definitions.Def_BookSixthRotations3` (theorem id 8b9bc6db-4515-4864-bece-38016a5ce502). The angle signs are forced: the accepted proof of `BookSixth.round_circle_single_standardize` uses, for each coordinate plane, the map at angle $t\theta$ together with its inverse at $-t\theta$ (see the `fun t x => ![Real.cos (t * θ) * x 0 - Real.sin (t * θ) * x 1, Real.cos (t * θ) * x 1 + Real.sin (t * θ) * x 0, x 2]` and its partner with both signs reversed). This supersedes the incorrect draft `BookSixth.rotTriple_mul_eq_one` (2775a585-e553-4a50-8ddb-817ccbd2c4cf), which asserted that the product at the SAME angles is its own inverse; that statement is false, since $R(\pi/4) R(\pi/4)$ has upper-left entry $\cos(\pi/2) = 0$ rather than $1$.

import Mathlib
import Definitions.Def_BookSixthRotations3
open Matrix
noncomputable section

theorem BookSixth.rotTriple_mul_inverse (θ1 θ2 θ3 : ℝ) :
    rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
      (rot12Matrix (-θ3) * rot02Matrix (-θ2) * rot01Matrix (-θ1)) = 1 := by sorry
