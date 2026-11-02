-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:42:58.262987+00:00
-- url     : https://prove2.me/theorems/89d85e84-1aea-42cb-ac41-e0b11d6aa537
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V <= M.edgeFinset.card + 6) := by sorry
