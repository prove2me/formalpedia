-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:53:54.548405+00:00
-- url     : https://prove2.me/theorems/4a969e66-8fd1-4221-94d7-5169ddd5a6af
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph with at least three vertices that has no strictly larger drawable supergraph on the same vertex set has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_1b39b828_58fc_4ef1_a477_eeaba85e9424
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
