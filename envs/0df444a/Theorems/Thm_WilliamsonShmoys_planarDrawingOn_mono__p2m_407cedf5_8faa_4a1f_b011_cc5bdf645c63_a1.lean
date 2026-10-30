-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:03.458763+00:00
-- url     : https://prove2.me/theorems/68b4b890-4686-40a9-b6a6-373b5eaeb673
-- title:
--   Planar drawing is inherited by subgraphs
-- statement:
--   If H is a subgraph of a graph K with a planar drawing on the same ordered vertex type, then H has a planar drawing on that vertex type. The independent proof route is to reuse K’s positions and arcs: every edge-specific condition for H follows from the corresponding condition for K because each H edge is a K edge. This removes the drawing-heredity step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1 {V : Type} [Fintype V] [LinearOrder V] {H K : SimpleGraph V} (hHK : H ≤ K) (hK : HasPlanarDrawingOn K) : HasPlanarDrawingOn H := by sorry
