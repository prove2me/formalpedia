-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_b456ae06_v4
-- name    : WilliamsonShmoys.maximal_planar_edge_count_b456ae06_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:11:57.845705+00:00
-- url     : https://prove2.me/theorems/2dcb7810-a089-4e3b-984d-958aef21b4d1
-- title:
--   Euler edge count for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_b456ae06_v4 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
