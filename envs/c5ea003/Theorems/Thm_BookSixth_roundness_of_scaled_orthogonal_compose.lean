-- Prove2me | Theorems.Thm_BookSixth_roundness_of_scaled_orthogonal_compose
-- name    : BookSixth.roundness_of_scaled_orthogonal_compose
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:50:32.510547+00:00
-- url     : https://prove2.me/theorems/ecc96804-f51a-4663-b726-d7531255d0ce
-- title:
--   Chapter 15 primitive: composing a roundness-preserving motion with a scaled orthogonal motion
-- statement:
--   Suppose $L$ is a motion that keeps the image of a round circle round at every time, and $G$ is a motion each of whose time maps is a positive scaling composed with an inner-product-preserving linear map and a translation, that is $G_t(x) = a_t A_t x + b_t$ with $a_t > 0$. Then the composite motion $x \mapsto G_t(L_t(x))$ also keeps the image of the round circle round at every time. This is the two-step composition rule that assembles a roundness-preserving ambient isotopy out of rigid and similarity pieces, and it is the rule that any inductive construction of the Chapter 15, Theorem 1 motion needs at each stage.
-- source:
--   Composition rule for the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The image identity `(fun s => G t (L t s)) '' C = G t '' (L t '' C)` is `Set.image_comp`, and the conclusion is the proved `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246) applied to the round circle `(L t) '' C`. This is the composition form of that theorem; the theorem itself covers only a single isotopy, so without this step one cannot chain stages of a multi-stage motion.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_rigid_similarity_isotopy
open BookSixth

theorem BookSixth.roundness_of_scaled_orthogonal_compose {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3, 0 < a ∧
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = a • (A x) + b))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
