-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:14.490094+00:00
-- url     : https://prove2.me/theorems/d166c073-f098-437a-9518-b472263b9dd9
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) : 3 * Fintype.card V ≤ Y.edgeSet.ncard + 6 := by sorry
