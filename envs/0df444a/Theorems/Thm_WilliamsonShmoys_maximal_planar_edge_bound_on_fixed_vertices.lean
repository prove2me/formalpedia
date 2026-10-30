-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_on_fixed_vertices
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:25:15.899515+00:00
-- url     : https://prove2.me/theorems/fe727e98-c766-43aa-839c-f06290f1244e
-- title:
--   Edge bound for an inclusion-maximal planar graph on fixed vertices
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ X : SimpleGraph V,
      G ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
