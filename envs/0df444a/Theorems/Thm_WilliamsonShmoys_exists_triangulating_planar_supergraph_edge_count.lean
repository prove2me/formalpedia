-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulating_planar_supergraph_edge_count
-- name    : WilliamsonShmoys.exists_triangulating_planar_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:41:08.887064+00:00
-- url     : https://prove2.me/theorems/71a098b3-0bc7-499f-9534-e042704115d1
-- title:
--   A drawable graph extends to a triangulation with the planar edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulating_planar_supergraph_edge_count {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
