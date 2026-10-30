-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_fixed_vertex_type
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_fixed_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:06:24.233987+00:00
-- url     : https://prove2.me/theorems/f255de1b-0f14-475d-ab9a-526a64231511
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   An inclusion-maximal simple planar graph on at least three vertices has at least 3|V| − 6 edges. This removes the planar topology and Euler-counting work from the parent. A proof route is to use the supplied drawing to obtain a plane embedding, show maximality forces every face to be triangular (including the cases of bridges or disconnected components by showing they admit a planar edge addition), and apply Euler’s formula. Since the graph is simple and |V| ≥ 3, the usual face-degree count gives the stated bound. The strict lower threshold preserves the three-vertex equality case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_bound_fixed_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V, H <= G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by sorry
