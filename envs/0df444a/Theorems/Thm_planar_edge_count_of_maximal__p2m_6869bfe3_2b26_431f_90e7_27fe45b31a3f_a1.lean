-- Prove2me | Theorems.Thm_planar_edge_count_of_maximal__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
-- name    : planar_edge_count_of_maximal__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:43.521062+00:00
-- url     : https://prove2.me/theorems/08fd48d6-806c-4668-a545-2d7d492a5c18
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_edge_count_of_maximal__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → LE.le M N → LE.le N M)
    (hV : LE.le 3 (Fintype.card V)) :
    LE.le (3 * Fintype.card V) (M.edgeSet.ncard + 6) := by
  sorry
