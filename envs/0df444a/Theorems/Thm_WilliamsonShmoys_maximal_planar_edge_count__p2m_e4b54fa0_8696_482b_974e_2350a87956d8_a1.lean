-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:18.491466+00:00
-- url     : https://prove2.me/theorems/d113e12d-71ad-41a3-b6a2-eff564f35d28
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) (hmax : ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet) : Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
