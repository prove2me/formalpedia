-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono_ctx816e1e7a
-- name    : WilliamsonShmoys.planar_edge_count_mono_ctx816e1e7a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:00:57.312176+00:00
-- url     : https://prove2.me/theorems/724216b8-51ea-4874-8e91-8715cb7adbf5
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, graph inclusion implies edge-count monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_mono_ctx816e1e7a
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
