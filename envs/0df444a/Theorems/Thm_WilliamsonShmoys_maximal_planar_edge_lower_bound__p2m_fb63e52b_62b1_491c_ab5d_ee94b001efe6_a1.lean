-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:10.151337+00:00
-- url     : https://prove2.me/theorems/4df8ba81-9f07-4595-bdbe-b174d2b4360b
-- title:
--   Maximality gives the planar edge lower bound
-- statement:
--   An inclusion-maximal graph under the given crossing-free drawing predicate, on at least three vertices, has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V <= H.edgeFinset.card + 6 := by sorry
