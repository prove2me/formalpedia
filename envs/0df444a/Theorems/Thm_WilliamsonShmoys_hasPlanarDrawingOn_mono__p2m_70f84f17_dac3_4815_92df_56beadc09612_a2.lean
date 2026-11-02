-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:12.276993+00:00
-- url     : https://prove2.me/theorems/207ab535-8da2-4cb0-92ce-ca263bd5fc5e
-- title:
--   Planar drawing is preserved by edge removal
-- statement:
--   A drawing witnessing `HasPlanarDrawingOn` for a graph also witnesses it for any subgraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_70f84f17_dac3_4815_92df_56beadc09612_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
