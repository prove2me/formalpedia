-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
-- name    : WilliamsonShmoys.planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:28:35.126897+00:00
-- url     : https://prove2.me/theorems/60d3732d-de87-4f83-bd89-d86a85290de0
-- title:
--   Extract finite face data from a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing admits finite face data recording Euler's equation, twice-per-edge boundary incidence, and degree at least three for every face. This child carries the geometric construction that is not represented by the supplied drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_exists_mapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : HasPlanarDrawingOn J)
    (hconn : forall u v : V, Nonempty (J.Walk u v))
    (hcard : 3 <= Fintype.card V) :
    Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) := by sorry
