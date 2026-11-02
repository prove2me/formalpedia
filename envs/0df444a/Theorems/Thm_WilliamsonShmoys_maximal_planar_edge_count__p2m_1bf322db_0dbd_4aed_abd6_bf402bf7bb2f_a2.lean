-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:22:59.085086+00:00
-- url     : https://prove2.me/theorems/b8afd70d-5e18-4708-a739-37d2bdc4e576
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-maximal simple planar graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to show maximality makes every face triangular, then use Euler’s formula and count face-edge incidences. At |V| = 3 the result gives the K₃ boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
