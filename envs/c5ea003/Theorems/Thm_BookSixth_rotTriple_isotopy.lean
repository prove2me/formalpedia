-- Prove2me | Theorems.Thm_BookSixth_rotTriple_isotopy
-- name    : BookSixth.rotTriple_isotopy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T04:50:22.035692+00:00
-- url     : https://prove2.me/theorems/65c29cc5-af69-412e-b2b1-d30a078ba724
-- title:
--   Chapter 15: the threefold coordinate rotation together with a translation is an isotopy
-- statement:
--   Let $\theta_1,\theta_2,\theta_3$ be real angles and $a$ a vector. Then $H_t x = R_t x + t a$, where $R_t$ is the threefold coordinate-plane rotation by the angles $t\theta_1, t\theta_2, t\theta_3$ composed in that order, is an ambient isotopy of $\mathbb{R}^3$: both $H_t$ and its inverse vary jointly continuously with $(t,x)$, $H_0$ is the identity, and the time map is exactly that formula. This isolates the rotational part of the standardising isotopy of a round circle, so that the remaining step only has to handle the uniform rescaling about the centre.
-- source:
--   Component of the roundness-preserving ambient motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. `rotTriple` is `((rot12CLM (t*θ3)).comp (rot02CLM (t*θ2))).comp (rot01CLM (t*θ1))` from the definition module `Definitions.Def_BookSixthRotations3` (theorem id 8b9bc6db-4515-4864-bece-38016a5ce502), whose inner-product preservation is the accepted `BookSixth.threefold_rotation_preserves_inner_product` (theorem id 38fc01a5-c2c4-4ee0-888a-c8ec2580ba0b). Continuity of the rotation family in time follows from `LinearMap.continuous_of_finiteDimensional` for the underlying matrix, valid because `Fin 3 -> R` is finite-dimensional; `fun_prop` cannot see through a matrix.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open BookSixth

theorem BookSixth.rotTriple_isotopy (θ1 θ2 θ3 : ℝ) (a : Space3) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ t x, H t x = rotTriple t θ1 θ2 θ3 x + t • a) := by sorry
