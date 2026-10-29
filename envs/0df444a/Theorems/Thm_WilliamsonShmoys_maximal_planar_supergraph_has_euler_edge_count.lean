-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_euler_edge_count
-- name    : WilliamsonShmoys.maximal_planar_supergraph_has_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:57:07.417789+00:00
-- url     : https://prove2.me/theorems/c22e36bc-25ad-4904-8a28-5c919901e1b4
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices is connected and has triangular faces in a planar embedding; Euler’s formula yields exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
