-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T06:23:31.403993+00:00
-- url     : https://prove2.me/theorems/2cc7db04-51a9-4164-8725-84656cb900d0
-- title:
--   Strict drawable extension of a disconnected graph
-- statement:
--   A disconnected finite graph with a crossing-free drawing has a strictly larger supergraph on the same vertices that also has a crossing-free drawing. This isolates the topological edge-addition step. The empty and connected cases are excluded by the disconnectedness hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
