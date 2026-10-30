-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:34:23.292038+00:00
-- url     : https://prove2.me/theorems/95c5e018-462a-437a-9f69-3e5e16e1f2db
-- title:
--   Lower edge bound for a maximal finite simple planar graph
-- statement:
--   A maximal finite simple graph with the supplied planar drawing and at least three vertices has at least 3|V|−6 edges. Maximality rules out a face that can be triangulated by adding an edge; triangulation and Euler's formula yield the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J →
      (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) → J = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
