-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_extension_same_vertex_type
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximal_extension_same_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:58:51.640032+00:00
-- url     : https://prove2.me/theorems/dfc866c8-a75f-4c5a-8333-ab529f7acf1a
-- title:
--   Maximal planar supergraph on the same vertex type
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a planar supergraph on the same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_maximal_extension_same_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by
  sorry
