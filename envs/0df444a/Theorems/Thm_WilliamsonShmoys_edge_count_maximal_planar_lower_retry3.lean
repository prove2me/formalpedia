-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_maximal_planar_lower_retry3
-- name    : WilliamsonShmoys.edge_count_maximal_planar_lower_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:36:01.974892+00:00
-- url     : https://prove2.me/theorems/7cbba167-dbe3-4e97-9632-fbcaaee0fd3e
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_maximal_planar_lower_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by sorry
