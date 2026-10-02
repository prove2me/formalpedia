-- Prove2me | Theorems.Thm_BookSixth_roundness_glue_on_ground
-- name    : BookSixth.roundness_glue_on_ground
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T00:26:33.58572+00:00
-- url     : https://prove2.me/theorems/14d04cd8-51b9-49d8-ac5a-bdfe1737312b
-- title:
--   Chapter 15: glue a roundness-preserving motion onto a roundness-preserving prefix
-- statement:
--   Let $C$ be a set and let $G$ and $L$ be two families of homeomorphisms of $\mathbb{R}^3$ indexed by real time. Suppose that the time maps of $G$ carry EVERY round circle to a round circle, and that the time maps of $L$ carry $C$ to a round circle at every time. Then the composite motion that first applies $L_t$ and then $G_t$ carries $C$ to a round circle at every time. This is the fully general gluing statement: the image of $C$ under the composite is the image of the intermediate round circle $(L_t) '' C$ under $G_t$, which is round by the hypothesis on $G$. It supersedes `BookSixth.roundness_compose_two_general` (b298bbf3-4b40-4805-9a44-ee0ad4d17a34), whose hypothesis was that $G_t$ carries only the single fixed set $C$ to a round circle; that is too weak, because the conclusion needs $G_t$ to carry the INTERMEDIATE set $(L_t) '' C$, which is a different round circle, and a map may preserve one round circle while squashing another.
-- source:
--   Corrected form of the gluing principle needed to assemble a roundness-preserving ambient motion for Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The set-theoretic core is `Set.image_comp`: the image of $C$ under the composite is the image of $(L_t) '' C$ under $G_t$. The hypothesis quantifies over ALL round circles rather than only the fixed set $C$, which is exactly what the conclusion requires. The accepted theorems `BookSixth.roundness_compose_two` and `BookSixth.roundness_of_scaled_orthogonal_compose` carry structured hypotheses on $G$ that also suffice; this statement is the unstructured general form.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.roundness_glue_on_ground {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3)
    (hGround : ∀ (D : Set Space3), ∀ t, RoundCircle D → RoundCircle ((G t) '' D))
    (L : ℝ → Space3 ≃ₜ Space3) (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by sorry
