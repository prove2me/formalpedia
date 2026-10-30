-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:46:41.847555+00:00
-- url     : https://prove2.me/theorems/b8d35c99-ccc1-4cae-8065-458ad4737ca1
-- title:
--   Planar graph completion with maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|-6 edges. This child contains the planar completion and Euler-counting work, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_3a9c85e5_093c_48f7_b644_f83c4d4db2f4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun K : SimpleGraph V => G <= K /\ HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
