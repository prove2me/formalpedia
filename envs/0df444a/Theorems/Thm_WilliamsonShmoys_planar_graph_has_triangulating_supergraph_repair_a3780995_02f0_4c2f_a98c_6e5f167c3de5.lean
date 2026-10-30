-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:09:33.509127+00:00
-- url     : https://prove2.me/theorems/b2159ba3-56d0-484f-a1bb-a554986b8930
-- title:
--   Drawable graphs have triangulating supergraphs
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulating_supergraph_repair_a3780995_02f0_4c2f_a98c_6e5f167c3de5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
