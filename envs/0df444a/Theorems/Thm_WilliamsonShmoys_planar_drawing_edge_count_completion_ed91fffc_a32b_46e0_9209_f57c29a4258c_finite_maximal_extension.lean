-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:47:37.397963+00:00
-- url     : https://prove2.me/theorems/c6e23028-317c-492b-89e8-8ec4b9740382
-- title:
--   Finite maximal drawing-preserving extension
-- statement:
--   Every finite graph with a planar drawing has a drawing-preserving supergraph on the same vertices that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K := by sorry
