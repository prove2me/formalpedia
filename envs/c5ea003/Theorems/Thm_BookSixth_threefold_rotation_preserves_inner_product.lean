-- Prove2me | Theorems.Thm_BookSixth_threefold_rotation_preserves_inner_product
-- name    : BookSixth.threefold_rotation_preserves_inner_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T01:01:11.09904+00:00
-- url     : https://prove2.me/theorems/38fc01a5-c2c4-4ee0-888a-c8ec2580ba0b
-- title:
--   Chapter 15: the threefold coordinate-plane rotation preserves the Euclidean inner product
-- statement:
--   Let $R_{01}$, $R_{02}$ and $R_{12}$ be the rotations of $\mathbb{R}^3$ in the coordinate planes $01$, $02$ and $12$ by the angles $t\theta_1$, $t\theta_2$ and $t\theta_3$, viewed as continuous linear maps. Then their composite preserves the Euclidean inner product: $\sum_i (R x)_i (R y)_i = \sum_i x_i y_i$ for all vectors $x,y$. Each single rotation preserves the inner product because $\cos^2\theta + \sin^2\theta = 1$, and the property is closed under composition. This is the admissible linear part $A$ in the roundness lemmas: the rotations of the standardising isotopy are not uniform scalings, so they must enter through an inner-product-preserving map rather than through a scalar.
-- source:
--   Structural ingredient for the roundness-preserving ambient motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The rotations are built as $3\times 3$ matrices lifted through `Matrix.mulVecLin` rather than through `ContinuousLinearMap.pi`, because `ContinuousLinearMap.pi` (`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/PiProd.lean:268`) takes a family `forall i, (phi i) ->L[R] (psi i)` whose source is a coordinate type, hence builds a DIAGONAL operator that cannot mix coordinates and so cannot express a rotation. Continuity is discharged by `LinearMap.continuous_of_finiteDimensional`, valid because `Fin 3 -> R` is finite-dimensional. Note that the norm on this type is the supremum norm, so the hypothesis must be stated as preservation of the bilinear form `sum i, x i * y i` and never as `norm (A x) = norm x`.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
open BookSixth

theorem BookSixth.threefold_rotation_preserves_inner_product (t θ1 θ2 θ3 : ℝ)
    (x y : (Fin 3 → ℝ)) :
    (∑ i, (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) x) i
        * (((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1)) y) i)
      = ∑ i, x i * y i := by sorry
