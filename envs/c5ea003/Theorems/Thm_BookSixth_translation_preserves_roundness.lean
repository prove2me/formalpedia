-- Prove2me | Theorems.Thm_BookSixth_translation_preserves_roundness
-- name    : BookSixth.translation_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T17:09:46.94143+00:00
-- url     : https://prove2.me/theorems/98e72aaa-f828-42fc-9d3f-0cfd12d8167b
-- title:
--   Chapter 15 primitive: translation preserves round circles
-- statement:
--   Let $C$ be a genuine round circle in $\mathbb{R}^3$, given as the radius-$r$ circle about a centre $c$ in the plane spanned by an orthonormal pair $u,v$. Then translating the plane by any vector $b$ gives another genuine round circle: the frame $u,v$ and the radius $r$ are unchanged and only the centre moves to $c + b$. This is one of the three rigid/similarity generators needed to move a circle to a standard place while every intermediate image stays round.
-- source:
--   Elementary interface consequence of the canonical sixth-edition definitions b1fcef2b-61fb-4326-bde6-cb6070d37c77. `RoundCircle` is by construction invariant under translation because the defining equations for the orthonormal frame and the radius are unchanged. Used as a generator in the roundness-preserving motion for Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.translation_preserves_roundness (C : Set Space3) (b : Space3)
    (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => x + b) '' C) := by sorry
