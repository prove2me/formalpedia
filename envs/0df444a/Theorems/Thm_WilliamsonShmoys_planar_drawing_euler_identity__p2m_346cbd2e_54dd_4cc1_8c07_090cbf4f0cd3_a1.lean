-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:43:13.08198+00:00
-- url     : https://prove2.me/theorems/3d3b374c-1e04-4711-a2c4-bf945c6d33b8
-- title:
--   Euler identity for a connected planar drawing
-- statement:
--   A connected graph equipped with a crossing-free drawing has a natural-number face count satisfying Euler’s formula. This isolates the Euler identity needed by the parent. A proof route is to derive a finite plane embedding from the supplied arcs and apply the connected plane-graph Euler formula, or prove it by induction while tracking how adding an embedded edge changes the faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hConnected : M.Connected)
    (hM : HasPlanarDrawingOn M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 := by sorry
