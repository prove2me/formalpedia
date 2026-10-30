-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e
-- name    : WilliamsonShmoys.edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:18:09.854012+00:00
-- url     : https://prove2.me/theorems/3b82d126-e709-4415-8ca8-5f65de9bffaa
-- title:
--   Maximal planar graphs have exactly 3n minus 6 edges
-- statement:
--   A planar graph on at least three vertices that is maximal under edge inclusion has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_same_vertex_edge_maximal_planar_d91007ea_2b83_4647_90f6_3b32f55c223e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      ∀ ⦃u v⦄, M.Adj u v → K.Adj u v) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
