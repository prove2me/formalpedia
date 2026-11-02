-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- name    : WilliamsonShmoys.planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:14.792319+00:00
-- url     : https://prove2.me/theorems/2f51f877-ca32-4203-b95c-98b96e4e40ad
-- title:
--   Planar drawings are inherited by subgraphs
-- statement:
--   If a graph has the specified crossing-free drawing, every subgraph on the same vertices has that drawing too.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {H K : SimpleGraph V} (hHK : H ≤ K)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
