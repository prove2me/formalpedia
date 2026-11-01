-- Prove2me | Theorems.Thm_WilliamsonShmoys_four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- name    : WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:12.371208+00:00
-- url     : https://prove2.me/theorems/e41ac761-3075-4705-af63-9968e7948806
-- title:
--   A complete four-vertex dart fiber has size three
-- statement:
--   Tail-`v` darts correspond to their distinct endpoints. Simplicity excludes `v`, while completeness includes every other vertex; the four-vertex cardinality then gives exactly three darts. Prove the count by constructing an equivalence between the dart fiber and the subtype of vertices unequal to `v`, then use `hV`. This isolates the graph-fiber count from the parent’s rotation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.four_vertex_complete_dart_fiber_card__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    [DecidableRel H.Adj]
    (hV : Fintype.card V = 4)
    (hcomplete : forall u v : V, Not (u = v) -> H.Adj u v) (v : V) :
    Fintype.card {a : H.Dart // a.fst = v} = 3 := by sorry
