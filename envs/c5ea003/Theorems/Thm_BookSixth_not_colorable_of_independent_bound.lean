-- Prove2me | Theorems.Thm_BookSixth_not_colorable_of_independent_bound
-- name    : BookSixth.not_colorable_of_independent_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T17:55:58.471438+00:00
-- url     : https://prove2.me/theorems/3b5d3be7-c808-415d-983d-1182a2d8c1b9
-- title:
--   Independent-set bound obstructs a finite coloring
-- statement:
--   Let $G$ be a simple graph on $N$ labeled vertices, and let $k,a$ be nonnegative integers. Suppose every independent vertex set has size at most $a$. If
--
--   $$ka<N,$$
--
--   then G has no proper coloring with k colors. This is the deterministic coloring obstruction used after the short-cycle deletion step in the high-girth, high-chromatic-number construction. It includes zero colors and empty graphs without additional positivity assumptions.
-- source:
--   Derived finite counting lemma for the authoritative target BookSixth.high_girth_chromatic, https://prove2.me/api/v1/theorems/492eed0e-887f-4c2f-b442-46dfedbca013, using HasColoring in definition b1fcef2b-61fb-4326-bde6-cb6070d37c77. This is an independently proved auxiliary statement, not a separately numbered quotation from the book. Parent source: Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 3, p. 314, https://doi.org/10.1007/978-3-662-57265-8_45.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open Finset BookSixth

theorem BookSixth.not_colorable_of_independent_bound {N k a : ℕ} (G : SimpleGraph (Fin N)) (hind : ∀ S : Finset (Fin N), (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) → S.card ≤ a) (hsize : k * a < N) : ¬ HasColoring G k := by sorry
