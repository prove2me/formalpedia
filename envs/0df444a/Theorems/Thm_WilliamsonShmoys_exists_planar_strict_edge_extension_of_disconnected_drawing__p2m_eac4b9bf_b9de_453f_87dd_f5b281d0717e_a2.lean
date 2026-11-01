-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a2
-- name    : WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:35.244874+00:00
-- url     : https://prove2.me/theorems/47afe67c-60e1-47f9-a634-1f5964e2e86e
-- title:
--   Planar edge extension for disconnected drawings with at least three vertices
-- statement:
--   A disconnected graph on at least three vertices with the specified planar drawing has a planar supergraph on the same vertex type that adds an edge between two distinct previously nonadjacent vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧
      ∃ L : SimpleGraph V,
        K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.Adj u v := by sorry
