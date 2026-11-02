-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:44.478703+00:00
-- url     : https://prove2.me/theorems/cec667e7-b432-426e-9cef-b901d387a12d
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph on at least three vertices that admits no drawable proper supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      (∀ {u v}, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ {u v}, L.Adj u v → K.Adj u v) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
