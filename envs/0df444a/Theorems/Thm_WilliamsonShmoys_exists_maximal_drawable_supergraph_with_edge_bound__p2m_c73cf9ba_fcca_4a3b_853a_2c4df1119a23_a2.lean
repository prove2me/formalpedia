-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:21:29.818875+00:00
-- url     : https://prove2.me/theorems/ff556b08-9bb8-4b65-af48-6c1ba6d375a5
-- title:
--   A maximal drawable supergraph with monotone edge count
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_with_edge_bound__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      G.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
