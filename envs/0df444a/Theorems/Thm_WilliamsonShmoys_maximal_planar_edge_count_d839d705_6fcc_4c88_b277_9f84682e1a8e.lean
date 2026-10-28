-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e
-- name    : WilliamsonShmoys.maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:13:35.89389+00:00
-- url     : https://prove2.me/theorems/aa4e0804-d96d-49c0-9cf6-2ab15e53ca31
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
