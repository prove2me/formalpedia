-- Prove2me | Theorems.Thm_BookSixth_roundness_compose_two
-- name    : BookSixth.roundness_compose_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:00:56.710276+00:00
-- url     : https://prove2.me/theorems/7f482851-1fbb-4a3a-b397-5a6943210fe5
-- title:
--   Chapter 15 primitive: composing a roundness-preserving step with a similarity isotopy
-- statement:
--   Suppose $L$ is a motion that keeps the image of a round circle round at every time, and $G$ is a motion each of whose time maps is a similarity of positive scale. Then the composite motion $x \mapsto G_t(L_t(x))$ also keeps the image of the round circle round at every time. This is the two-step composition rule for assembling a roundness-preserving ambient isotopy out of rigid and similarity pieces.
-- source:
--   Composition rule for the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The image identity `(fun s => G t (L t s)) '' C = G t '' (L t '' C)` is `Set.image_comp`, and the conclusion is `BookSixth.roundness_of_similarity_isotopy` applied to the round circle `(L t) '' C`.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_similarity_isotopy
open BookSixth

theorem BookSixth.roundness_compose_two {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3)
    (hGsim : ∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (G t) x = (q.1 • x) + q.2))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
