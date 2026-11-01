-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:12.113193+00:00
-- url     : https://prove2.me/theorems/649933f7-19ec-4f62-a5e6-2469237e8943
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := dM
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
