-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:27:40.070348+00:00
-- url     : https://prove2.me/theorems/eec88a46-e2f1-426a-bbcb-0322b031599d
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and is inclusion-maximal among drawable supergraphs, then it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.Connected := by sorry
