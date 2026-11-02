-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2
-- name    : WilliamsonShmoys.planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:25:59.235293+00:00
-- url     : https://prove2.me/theorems/a95b2e09-031c-4e18-b347-423c7cdf2425
-- title:
--   Sparse planar drawings admit a strict planar extension
-- statement:
--   Every connected graph on at least three vertices with a crossing-free drawing and fewer than 3n−6 edges has a crossing-free supergraph on the same vertices that strictly contains it. This is the augmentation step used to contradict the parent theorem’s maximality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsmall : H.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧ ¬ J ≤ H := by sorry
