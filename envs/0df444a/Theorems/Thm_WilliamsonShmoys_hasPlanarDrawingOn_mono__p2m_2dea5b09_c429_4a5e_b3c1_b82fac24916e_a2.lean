-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:25.954025+00:00
-- url     : https://prove2.me/theorems/8dbda68c-7749-4743-9c74-cb7c92600517
-- title:
--   Planar drawings are preserved when edges are deleted
-- statement:
--   If a graph on a finite linearly ordered vertex type has a planar drawing, then any graph on that same type whose edges are a subset also has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G) :
    WilliamsonShmoys.HasPlanarDrawingOn G →
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
