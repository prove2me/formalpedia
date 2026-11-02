-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
-- name    : WilliamsonShmoys_planar_drawing_bridge_step__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:15.838071+00:00
-- url     : https://prove2.me/theorems/27083d0e-240f-44e7-ab87-c3e5b1ab8bad
-- title:
--   Add a drawable edge between components
-- statement:
--   Given a disconnected finite planar drawing, add a planar edge extension containing an edge between two vertices that were in different connected components. The non-reachability hypothesis ensures the new edge joins distinct components; the geometry to establish is that such an edge can be drawn without crossings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_planar_drawing_bridge_step__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hDisconnected : ¬ H.Connected) :
    ∃ L : SimpleGraph V, ∃ u v : V,
      H ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ H.Reachable u v ∧ L.Adj u v := by sorry
