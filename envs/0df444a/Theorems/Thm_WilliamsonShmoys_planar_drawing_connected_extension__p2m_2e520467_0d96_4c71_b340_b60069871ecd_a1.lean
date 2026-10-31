-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:55.402521+00:00
-- url     : https://prove2.me/theorems/a22916a4-7a8b-4f53-bd03-4020e8e3faca
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
