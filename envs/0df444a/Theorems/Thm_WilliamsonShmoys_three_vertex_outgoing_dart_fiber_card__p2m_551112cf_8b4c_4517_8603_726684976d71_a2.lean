-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a2
-- name    : WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:13.900567+00:00
-- url     : https://prove2.me/theorems/fb78d323-b464-4900-9593-58dbdf77951b
-- title:
--   Each vertex has exactly two outgoing darts in a complete three-vertex graph
-- statement:
--   In a simple graph with three vertices where every distinct pair is adjacent, exactly two darts have any fixed vertex as their tail.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 3)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v)
    [DecidableRel H.Adj]
    (v : V) :
    Fintype.card {d : H.Dart // d.fst = v} = 2 := by sorry
