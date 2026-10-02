-- Prove2me | Theorems.Thm_BookSixth_shrinking_similarity_scale_positive
-- name    : BookSixth.shrinking_similarity_scale_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T02:04:48.95292+00:00
-- url     : https://prove2.me/theorems/94e495b4-756f-4ef6-a4e9-e98428b98815
-- title:
--   Chapter 15: the scale of a shrinking similarity is positive on the half-open strip
-- statement:
--   On the half-open interval $[0,1)$ the scale factor $1-t$ of the shrinking similarity $K_t(x) = (1-t)\,x + t\,c$ is strictly positive. This is the exact positivity hypothesis needed to apply the accepted global-similarity roundness lemma `BookSixth.similarity_preserves_roundness`, and it is what makes $K_t$ invertible there. The bound is sharp: at $t=1$ the scale vanishes and $K_1$ collapses to the constant map $c$, which is why the shrinking motion cannot be extended past $t=1$ as a family of homeomorphisms.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the scale positivity needed by the single-circle shrinking motion.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.shrinking_similarity_scale_positive (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 1 - t := by sorry
