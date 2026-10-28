-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:32.240544+00:00
-- url     : https://prove2.me/theorems/08343436-3ed5-44fc-aeba-2ee2e4a22301
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has at least 3|V|−6 edges. The independent proof route is to show maximality makes the drawing connected and every face triangular, then count face-edge incidences and apply Euler's formula. The lower bound on |V| is needed for the triangulation edge count, including the three-vertex boundary case. This child isolates the topological and counting work left after the parent selects a maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
