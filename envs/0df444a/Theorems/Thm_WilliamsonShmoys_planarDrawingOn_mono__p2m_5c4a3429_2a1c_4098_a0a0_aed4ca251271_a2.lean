-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:36.376663+00:00
-- url     : https://prove2.me/theorems/dd3b0a02-4960-4a74-b421-56314169fb2e
-- title:
--   Planar drawing property is preserved by edge removal
-- statement:
--   If G is a subgraph of H and H has a planar drawing in the defined sense, then G has a planar drawing in the same sense.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_5c4a3429_2a1c_4098_a0a0_aed4ca251271_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  sorry
