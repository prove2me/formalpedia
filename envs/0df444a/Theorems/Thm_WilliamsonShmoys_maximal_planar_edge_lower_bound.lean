-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:26:20.071321+00:00
-- url     : https://prove2.me/theorems/2bcdf41a-362b-4f86-aa70-8c17ae77f9c5
-- title:
--   Maximal planarity forces at least the triangulation edge count
-- statement:
--   A planar graph that is maximal among planar supergraphs on the same vertex set and has at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  sorry
