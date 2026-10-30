-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:47.01809+00:00
-- url     : https://prove2.me/theorems/ceea82b2-e199-492c-ad5d-a194ae5752ca
-- title:
--   Triangulated drawable supergraph
-- statement:
--   A drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
