-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a1
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:22.613327+00:00
-- url     : https://prove2.me/theorems/fb9c08f9-b228-481d-9ea9-134d8142a46d
-- title:
--   Every finite planar drawing has a connected planar supergraph
-- statement:
--   Every graph with a finite crossing-free drawing can be extended, without adding vertices, to a connected graph that still has a crossing-free drawing. This child removes the topological extension work from the parent; the parent applies maximality to the resulting supergraph. Its boundary cases include empty and singleton vertex types, where the original graph is already connected. An independent proof route is to join embedded components successively by simple arcs in the complement, using vertices accessible from the unbounded face. The substantive remaining obligation is to formalize that arc construction for the exact continuous-arc and intersection conditions in HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun P : SimpleGraph V =>
      N <= P /\ P.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
