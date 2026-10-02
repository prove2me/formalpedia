-- Prove2me | Theorems.Thm_BookSixth_roundness_of_rigid_translate_compose
-- name    : BookSixth.roundness_of_rigid_translate_compose
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:31:16.014994+00:00
-- url     : https://prove2.me/theorems/7c78da12-7521-4a99-bb23-6007ae18743e
-- title:
--   Chapter 15 primitive: two rigid motions in sequence keep every image round
-- statement:
--   Suppose $L$ is a motion that keeps the image of a round circle round at every time, and $G$ is a motion each of whose time maps is a rigid motion. Then the composite motion $x \mapsto G_t(L_t(x))$ also keeps the image of the round circle round at every time. This is the two-step composition rule for assembling a roundness-preserving ambient isotopy out of rigid pieces, and it is the rule that a construction using only rotations and translations needs.
-- source:
--   Composition rule for the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The image identity `(fun s => G t (L t s)) '' C = G t '' (L t '' C)` is `Set.image_comp`, and the conclusion is `BookSixth.roundness_of_rigid_isotopy` applied to the round circle `(L t) '' C`.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_rigid_isotopy
open BookSixth

theorem BookSixth.roundness_of_rigid_translate_compose {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = (A x) + q.2))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
