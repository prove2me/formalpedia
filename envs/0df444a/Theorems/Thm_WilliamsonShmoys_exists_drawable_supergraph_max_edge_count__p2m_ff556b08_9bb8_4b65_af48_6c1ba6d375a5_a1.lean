-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:43.747358+00:00
-- url     : https://prove2.me/theorems/500f45b8-41b0-41c1-b502-b493b9fa57e8
-- title:
--   Finite edge-count maximizer among drawable supergraphs
-- statement:
--   For a drawable finite graph, some drawable supergraph has edge count at least that of every drawable supergraph containing it. This removes the finite optimization step from the parent; prove it by considering the finite type of all simple graphs on V and maximizing edge count over the eligible graphs. The empty/small-vertex cases are covered because G itself is eligible.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) := by sorry
