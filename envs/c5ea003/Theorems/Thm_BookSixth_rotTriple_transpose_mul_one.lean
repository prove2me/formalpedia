-- Prove2me | Theorems.Thm_BookSixth_rotTriple_transpose_mul_one
-- name    : BookSixth.rotTriple_transpose_mul_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T01:05:46.62102+00:00
-- url     : https://prove2.me/theorems/dfa71cd2-9c0d-4b93-99eb-5d7a5ec69872
-- title:
--   Chapter 15: the threefold coordinate rotation is orthogonal
-- statement:
--   The product of the three coordinate-plane rotations in $\mathbb{R}^3$ is an orthogonal matrix: its transpose is its inverse. Each factor is a rotation in a coordinate plane, so each satisfies $R^{\mathsf T} R = I$, using $\cos^2 + \sin^2 = 1$; the product of matrices that are right-invertible is again right-invertible, and associativity plus the identity laws collapse the composite product to $I$. This is the algebraic heart of `BookSixth.rotTriple_isotopy`: it is what makes the inverse leg of the isotopy $H t x = \mathrm{rotTriple}\, t\, x + t \bullet a$ expressible as a transpose, namely $(H t)^{-1} y = R(t)^{\mathsf T} \bullet y - t \bullet (R(t)^{\mathsf T} \bullet a)$. It is deliberately NOT `BookSixth.rotTriple_mul_inverse` or `BookSixth.rotTriple_mul_eq_one`, both of which are Disproved because they wrote the inverse in forward order, or omitted the transpose; here the transpose is the true transpose, and the order is the true product order.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the orthogonality of the threefold coordinate rotation used by the standardising isotopy.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
open scoped BigOperators
open scoped Matrix
open BookSixth

theorem BookSixth.rotTriple_transpose_mul_one (θ1 θ2 θ3 : ℝ) :
    (rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1)ᵀ *
      (rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1) = 1 := by sorry
