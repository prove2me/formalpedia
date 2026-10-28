-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_f663d05c
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_f663d05c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:35:28.055835+00:00
-- url     : https://prove2.me/theorems/d07c7eac-2ced-4931-9427-f5e6e6b64d9b
-- title:
--   Maximality forces the triangulation edge count
-- statement:
--   An inclusion-maximal graph under the supplied planar-drawing predicate, on at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_f663d05c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
