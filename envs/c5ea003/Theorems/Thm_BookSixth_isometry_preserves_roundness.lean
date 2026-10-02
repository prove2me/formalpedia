-- Prove2me | Theorems.Thm_BookSixth_isometry_preserves_roundness
-- name    : BookSixth.isometry_preserves_roundness
-- status  : Open
-- author  : @WillR
-- created : 2026-09-25T17:57:38.953074+00:00
-- url     : https://prove2.me/theorems/308bb418-1d47-40a8-99c8-f9203e582869
-- title:
--   Chapter 15 primitive: a norm-preserving linear map composed with a positive scaling and a translation preserves round circles
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$, given by a centre $c$, an orthonormal pair $u,v$ and a radius $r>0$. Let $A$ be a linear map of $\mathbb{R}^3$ that preserves lengths, and let $a>0$ and $b$ be a scale and a translation. Then the image of $C$ under $x \mapsto a\,A x + b$ is again a genuine round circle, with centre $a\,A c + b$, orthonormal frame $A u, A v$ and radius $a r$. This single statement subsumes the three coordinate-plane rotations: a rotation about a coordinate axis is a particular length-preserving linear map. The frame equations follow because a length-preserving linear map sends vectors of norm one to vectors of norm one, and the radius follows because lengths scale by $a>0$.
-- source:
--   Generalisation of the proved coordinate-rotation theorems `BookSixth.rotation_01_preserves_roundness` (c6ef30d4-c446-409d-aa34-03f8d08c572b), `BookSixth.rotation_02_preserves_roundness` (4478bed1-0d6e-4012-9891-30b067f6f731) and `BookSixth.rotation_12_preserves_roundness` (f890bc0d-54b1-4686-a4d6-d785f5ecf93c), and of `BookSixth.similarity_preserves_roundness` (050cc58c-fca3-4342-912b-c3ad3825e5ec). The class of maps of the form $x \mapsto a A x + b$ with $A$ length-preserving and $a>0$ is the genuinely closed class under composition, whereas uniform scalings and translations are closed but the three coordinate rotations taken together are not closed among themselves. Used in the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.isometry_preserves_roundness (C : Set Space3)
    (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (b : Space3) (a : ℝ)
    (hA : ∀ x : Space3, ‖A x‖ = ‖x‖) (ha : 0 < a) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • (A x) + b) '' C) := by sorry
