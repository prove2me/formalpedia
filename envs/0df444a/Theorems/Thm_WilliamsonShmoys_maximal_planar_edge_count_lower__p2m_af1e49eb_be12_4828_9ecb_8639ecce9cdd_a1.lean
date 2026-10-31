-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:01.136533+00:00
-- url     : https://prove2.me/theorems/4d6c0a35-6002-42fd-b1db-c7f140706d86
-- title:
--   Maximality forces the matching edge lower bound
-- statement:
--   If a drawable simple graph on at least three vertices has no drawable proper supergraph on the same vertices, then it has at least 3n − 6 edges. A proof route is to show every missing edge can be added to a maximal planar embedding unless all faces are triangles, and then apply Euler’s formula; the n = 3 case is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
