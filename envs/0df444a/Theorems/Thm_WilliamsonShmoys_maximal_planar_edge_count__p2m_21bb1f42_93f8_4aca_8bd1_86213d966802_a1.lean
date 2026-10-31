-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:44.219571+00:00
-- url     : https://prove2.me/theorems/250c621e-cf82-4b35-b482-74352cb82491
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable graphs on its vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
