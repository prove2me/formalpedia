-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:34:58.436985+00:00
-- url     : https://prove2.me/theorems/8122a02e-177a-44bd-9de8-e1e79416f7a3
-- title:
--   Connected planar augmentation on the same vertices
-- statement:
--   Any finite graph with a planar drawing and at least three vertices has a connected planar supergraph on the same vertex set whose edge count is at least the original graph’s. The explicit decidability witness makes the supergraph’s edge finset available in the statement. Prove by connecting the components through the complement of the drawing, preserving the existing edges. The hard remaining work is constructing the added arcs and checking the drawing’s endpoint and nonintersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V), ∃ (dM : DecidableRel M.Adj),
      (letI : DecidableRel M.Adj := dM
       HasPlanarDrawingOn M ∧
       N.edgeFinset.card ≤ M.edgeFinset.card ∧
       M.Connected) := by sorry
