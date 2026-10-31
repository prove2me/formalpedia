-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:37:13.419252+00:00
-- url     : https://prove2.me/theorems/1340efd2-e406-4746-997b-d7e230feab14
-- title:
--   Planar drawings are preserved by taking subgraphs
-- statement:
--   If a graph has a crossing-free drawing and `G` is its subgraph on the same vertices, then `G` also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
    {V : Type} [Fintype V] [LinearOrder V] {G J : SimpleGraph V}
    (hGJ : G ≤ J) (hJ : HasPlanarDrawingOn J) : HasPlanarDrawingOn G := by
  sorry
