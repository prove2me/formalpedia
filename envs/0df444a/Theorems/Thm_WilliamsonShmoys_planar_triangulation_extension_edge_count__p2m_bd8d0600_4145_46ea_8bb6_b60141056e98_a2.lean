-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_bd8d0600_4145_46ea_8bb6_b60141056e98_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_bd8d0600_4145_46ea_8bb6_b60141056e98_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:20.281192+00:00
-- url     : https://prove2.me/theorems/fb4066de-7283-4f38-a89f-c849e2980761
-- title:
--   Triangulation extension edge count for a planar drawing
-- statement:
--   Every drawable simple graph on at least three vertices extends, using the same vertex type, to a drawable simple graph with exactly 3|V|−6 edges. The child must address the exact continuous-arc drawing definition, including disconnected drawings and the three-vertex boundary. Given this extension, maximality in the parent forces the original graph and extension to have identical adjacency, yielding the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_bd8d0600_4145_46ea_8bb6_b60141056e98_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ (J : SimpleGraph V) (dJ : DecidableRel J.Adj),
      HasPlanarDrawingOn J ∧
      (∀ u v, H.Adj u v → J.Adj u v) ∧
      (letI : DecidableRel J.Adj := dJ;
       J.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
