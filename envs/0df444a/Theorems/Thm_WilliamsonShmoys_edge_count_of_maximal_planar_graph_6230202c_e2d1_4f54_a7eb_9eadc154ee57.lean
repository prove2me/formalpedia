-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:43:08.600049+00:00
-- url     : https://prove2.me/theorems/efeaf4fc-4504-4788-8f8b-7a26b6f9d0b9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex set has exactly 3|V|−6 edges. For three vertices maximality forces all three edges; for larger cases, maximality forces triangular faces and Euler’s formula yields the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
