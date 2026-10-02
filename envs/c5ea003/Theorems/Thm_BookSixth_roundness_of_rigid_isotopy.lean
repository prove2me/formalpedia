-- Prove2me | Theorems.Thm_BookSixth_roundness_of_rigid_isotopy
-- name    : BookSixth.roundness_of_rigid_isotopy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:11:31.263983+00:00
-- url     : https://prove2.me/theorems/fafe1771-4766-4182-8a79-4768ebb79cf6
-- title:
--   Chapter 15 primitive: a family of rigid motions keeps every image round
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$, given by a centre $c$, an orthonormal pair $u,v$ and a positive radius. Let $G$ be a family of homeomorphisms of $\mathbb{R}^3$ such that at every time $t$ the map $G_t$ is a rigid motion, that is a translation composed with a linear map preserving the Euclidean inner product. Then every intermediate image $G_t(C)$ is again a genuine round circle, with centre $G_t(c)$, orthonormal frame $A_t u$, $A_t v$ and the same radius. This is the time-indexed form of `BookSixth.euclidean_isometry_preserves_roundness` and is the composition rule for building a motion out of rigid pieces. It is the key lemma for the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, because a product of any number of rotations and translations is again of the form $x \mapsto A x + b$ with $A$ orthogonal.
-- source:
--   Immediate application of the proved theorem `BookSixth.euclidean_isometry_preserves_roundness` (theorem id 837c17d9-c673-4779-a8ad-cb78680fc3a4) at the scale a = 1, applied at each time, with the pointwise hypothesis turned into an image equality by `Set.image_congr'`. The hypothesis is stated as preservation of the bilinear form $\sum_i x_i y_i$ rather than of the norm, because the norm on the type `Fin 3 → ℝ` in these definitions is the supremum norm, not the Euclidean norm. Used in the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.roundness_of_rigid_isotopy {C : Set Space3}
    (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = (A x) + q.2)) :
    ∀ t, RoundCircle ((G t) '' C) := by sorry
