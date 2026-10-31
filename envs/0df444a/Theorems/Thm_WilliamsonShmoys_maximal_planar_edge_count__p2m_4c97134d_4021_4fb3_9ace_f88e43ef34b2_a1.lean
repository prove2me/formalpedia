-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:10.199335+00:00
-- url     : https://prove2.me/theorems/fcb8ec4c-c30d-44dd-a4d8-def1801ee290
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph with at least three vertices that has no proper drawable supergraph on that vertex set has exactly 3|V|−6 edges. This is the standard maximal planar graph edge-count result; its proof route uses Euler’s formula and the fact that maximality forces a triangulation. The three-vertex boundary is included, where the count is three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
