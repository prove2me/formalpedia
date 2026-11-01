-- Prove2me | Theorems.Thm_WilliamsonShmoys_four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- name    : WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:55.904491+00:00
-- url     : https://prove2.me/theorems/75f329f4-68bb-4d41-9ccf-c562bc4dab9d
-- title:
--   A complete four-vertex dart fiber has size three
-- statement:
--   Darts with tail `v` correspond to vertices adjacent to `v`. The graph is loopless, and completeness makes every other vertex adjacent, so the four-vertex hypothesis gives a fiber of size three. The explicit adjacency decidability supplies the finite subtype instances needed to state the cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    [DecidableRel H.Adj]
    (hV : Fintype.card V = 4)
    (hcomplete : forall u v : V, u ≠ v -> H.Adj u v) (v : V) :
    Fintype.card {a : H.Dart // a.fst = v} = 3 := by
  sorry
