-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_e61f28a9_retry3
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_e61f28a9_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:03:48.444405+00:00
-- url     : https://prove2.me/theorems/f13c6f01-29f8-4b04-b672-259d7d584830
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph on at least three vertices has exactly 3|V|−6 edges. The proof uses maximality to establish a triangulated plane embedding, followed by Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_e61f28a9_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
