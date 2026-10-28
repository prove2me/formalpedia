-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_euler_edge_count
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:43:33.357282+00:00
-- url     : https://prove2.me/theorems/1232b949-3cf7-4692-bbec-1ac60480743c
-- title:
--   An edge-maximal planar drawing has the Euler edge count
-- statement:
--   An edge-maximal graph with a drawing satisfying HasPlanarDrawingOn has exactly three times the number of vertices minus six edges, provided it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
