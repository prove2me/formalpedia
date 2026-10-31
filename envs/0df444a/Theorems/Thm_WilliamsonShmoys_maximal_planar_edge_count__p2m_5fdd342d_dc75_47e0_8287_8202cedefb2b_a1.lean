-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:35.467188+00:00
-- url     : https://prove2.me/theorems/44670f2d-dc1c-47be-9f76-298ca920e2c7
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite drawable simple graph with at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. A proof route is to show maximality forces a triangulation and then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
