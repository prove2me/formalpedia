-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:31.84298+00:00
-- url     : https://prove2.me/theorems/d731af9b-3e3c-4abd-b784-64639da6b67a
-- title:
--   Maximal drawable graphs meet the planar edge bound
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that has no strict drawable supergraph on those vertices has at least 3|U|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (L : SimpleGraph U)
    (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph U, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card U - 6 ≤ L.edgeSet.ncard := by sorry
