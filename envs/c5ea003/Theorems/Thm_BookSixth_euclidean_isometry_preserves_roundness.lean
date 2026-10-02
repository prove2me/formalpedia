-- Prove2me | Theorems.Thm_BookSixth_euclidean_isometry_preserves_roundness
-- name    : BookSixth.euclidean_isometry_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:05:45.775257+00:00
-- url     : https://prove2.me/theorems/837c17d9-c673-4779-a8ad-cb78680fc3a4
-- title:
--   Chapter 15 primitive: a Euclidean-orthogonal linear map, a positive scaling and a translation preserve round circles
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$, given by a centre $c$, an orthonormal pair $u,v$ and a radius $r>0$. Let $A$ be a real linear map of $\mathbb{R}^3$ that preserves the Euclidean inner product, let $a>0$, and let $b$ be a vector. Then the image of $C$ under $x \mapsto a\,A x + b$ is again a genuine round circle, with centre $a\,A c + b$, orthonormal frame $A u, A v$ and radius $a r$. The frame equations are immediate: $A$ sends the inner product of $u$ with itself, of $v$ with itself, and of $u$ with $v$ to the same three values $1$, $1$ and $0$. Note that the hypothesis is stated as preservation of the inner product $\sum_i x_i y_i$ rather than of the norm, because the norm on the type `Fin 3 → ℝ` in these definitions is the supremum norm, not the Euclidean norm; a rotation by $120^\circ$ about an axis preserves Euclidean lengths but not the supremum norm. This single statement subsumes the three proved coordinate-plane rotation theorems, since a coordinate-plane rotation is a particular inner-product-preserving linear map.
-- source:
--   Correct generalisation of the proved theorems `BookSixth.rotation_01_preserves_roundness` (c6ef30d4-c446-409d-aa34-03f8d08c572b), `BookSixth.rotation_02_preserves_roundness` (4478bed1-0d6e-4012-9891-30b067f6f731), `BookSixth.rotation_12_preserves_roundness` (f890bc0d-54b1-4686-a4d6-d785f5ecf93c) and `BookSixth.similarity_preserves_roundness` (050cc58c-fca3-4342-912b-c3ad3825e5ec). The class of maps $x \mapsto a A x + b$ with $A$ inner-product preserving and $a>0$ is genuinely closed under composition, whereas uniform scalings and translations are closed but the three coordinate-plane rotations are not closed among themselves. Used in the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. This supersedes the earlier draft `BookSixth.isometry_preserves_roundness` (308bb418-1d47-40a8-99c8-f9203e582869), whose hypothesis `∀ x, ‖A x‖ = ‖x‖` wrongly refers to the supremum norm on `Fin 3 → ℝ`.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.euclidean_isometry_preserves_roundness (C : Set Space3)
    (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (b : Space3) (a : ℝ)
    (hA : ∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i)
    (ha : 0 < a) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • (A x) + b) '' C) := by sorry
